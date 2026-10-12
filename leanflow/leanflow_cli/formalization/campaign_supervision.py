"""Keep bounded HDP waves alive through task quarantine and service cooldowns."""

from __future__ import annotations

import json
import signal
import subprocess
import time
from datetime import UTC, datetime
from pathlib import Path
from types import SimpleNamespace
from typing import Any

from agent.accounting.provider_quota_budget import read_quota_budget
from core.utils import atomic_json_write
from leanflow_cli.formalization.campaign_recovery import dependent_exclusions


def supervise_continuously(
    options: Any,
    scale: dict[str, Any],
    *,
    root: Path,
    now: Any = time.time,
    pause: Any = time.sleep,
) -> dict[str, Any]:
    """Run until deadline/STOP/quota exhaustion, without treating task failures as success."""
    options.log_dir.mkdir(parents=True, exist_ok=True)
    deadline = now() + options.hours * 3600
    stop = options.log_dir / "STOP"
    campaign = root / "fate-x-work/HDP/Environments/campaign.json"
    project = root / "fate-x-work"
    hashes = scale["source_hashes"]()
    # Wave concurrency comes from the caller. It used to be hard-coded to 4
    # here, which silently overrode the supervisor's own setting: every
    # hdp-long-run launch between 2026-09-18 and 2026-10-03 recorded 4 workers
    # and never dispatched more than four at once, no matter what the launcher
    # asked for. Keep 4 as the default so an omitted value behaves as before.
    workers = max(1, int(getattr(options, "workers", 4) or 4))
    excluded = dependent_exclusions(campaign, set(options.defer_batch))
    failures: dict[str, int] = {}
    retry_streak = 0
    pending = None
    state: dict[str, Any] = {
        "started_at": datetime.fromtimestamp(now(), UTC).isoformat(),
        "deadline_utc": datetime.fromtimestamp(deadline, UTC).isoformat(),
        "status": "starting",
        "continuous": True,
        "workers": workers,
        "stage": "mixed",
        "quota_budget": str(options.budget),
        "budget_extension_allowed": False,
        "extension_activated": False,
        "waves": [],
        "remote_warmup": [],
        "deferred_batches": sorted(excluded),
        "cooldowns_used": 0,
    }

    checkpoint = options.log_dir / "checkpoint.json"
    if checkpoint.exists():
        saved = json.loads(checkpoint.read_text())
        if saved["state"]["quota_budget"] != str(options.budget):
            raise ValueError("cannot change the ledger while resuming a supervisor")
        state = saved["state"]
        state.pop("finished_at", None)
        deadline = datetime.fromisoformat(state["deadline_utc"]).timestamp()
        excluded = set(saved["excluded"])
        failures = saved["failures"]
        retry_streak = saved["retry_streak"]
        pending = saved["pending"]
        hashes = saved["hashes"]
        if pending is None and state.get("active_wave_path"):
            pending = json.loads(Path(state["active_wave_path"]).read_text())

    def save() -> None:
        state["heartbeat_utc"] = datetime.fromtimestamp(now(), UTC).isoformat()
        atomic_json_write(options.log_dir / "status.json", state)
        atomic_json_write(
            checkpoint,
            {
                "state": state,
                "excluded": sorted(excluded),
                "failures": failures,
                "retry_streak": retry_streak,
                "pending": pending,
                "hashes": hashes,
            },
        )

    def wait(reason: str, seconds: float) -> None:
        resume = min(deadline, now() + seconds)
        state.update(status=reason, resume_at_utc=datetime.fromtimestamp(resume, UTC).isoformat())
        state["cooldowns_used"] += 1
        save()
        while now() < resume and not stop.exists():
            pause(min(15, resume - now()))
            save()

    def wave_created(path: Path) -> None:
        state["active_wave_path"] = str(path)
        save()

    def on_stop(_sig: int, _frame: Any) -> None:
        stop.touch()

    handlers = {sig: signal.signal(sig, on_stop) for sig in (signal.SIGINT, signal.SIGTERM)}
    save()
    try:
        if state.get("resume_at_utc"):
            resume_at = min(deadline, datetime.fromisoformat(state["resume_at_utc"]).timestamp())
            while now() < resume_at and not stop.exists():
                pause(min(15, resume_at - now()))
                save()
        while (now() < deadline and not stop.exists()) or pending is not None:
            if scale["source_hashes"]() != hashes:
                state["status"] = "source_changed"
                break
            if pending is not None:
                state["status"] = "recovering_tasks"
                save()
                if not scale["recover_continuous_wave"](pending, campaign, project):
                    state["recovery_wait"] = pending.get("recovery_wait", {})
                    if now() >= deadline or stop.exists():
                        state["status"] = "recovery_pending_at_stop"
                        break
                    wait("waiting_for_recovery", 60)
                    continue
                state.pop("recovery_wait", None)
                provider_failed = False
                accepted = 0
                for item in pending.get("items", []):
                    kind = item.get("classification")
                    batch_id = item["batch_id"]
                    if kind == "accepted":
                        accepted += 1
                        continue
                    if item.get("safe_to_continue") or kind == "semantic":
                        excluded.add(batch_id)
                    elif kind in {"infrastructure", "rate_limit", "relay_transient"}:
                        failures[batch_id] = failures.get(batch_id, 0) + 1
                        # Finite paid retries per item; prolonged outages wait at
                        # supervisor level, never erase the quota's unknown holds.
                        if failures[batch_id] >= 3:
                            excluded.add(batch_id)
                        provider_failed = True
                    elif kind in {"auth", "quota"}:
                        diagnostics = " ".join(
                            str(a.get("final_diagnostic", "")) for a in item.get("new_attempts", [])
                        )
                        if (
                            kind == "quota"
                            and "provider quota budget does not cover the request reservation"
                            in diagnostics
                        ):
                            # Other drained workers may have settled their holds;
                            # re-read the same ledger before deciding exhaustion.
                            continue
                        if kind == "quota" and "quote observation is expired" in diagnostics:
                            # Not a budget problem: the run outlived its pricing
                            # quote. The 2026-10-06 run died at 02:04:01 UTC with
                            # 128.7M of its 267.9M limit unspent, sixteen seconds
                            # after the quote taken at 02:03:45 UTC aged past its
                            # twenty-four hours. Report it as what it is, so an
                            # operator refreshes the quote instead of topping up a
                            # ledger that was never short.
                            state["status"] = "quote_expired"
                            state["quote_expired_diagnostic"] = diagnostics[:500]
                            save()
                            return state
                        if kind == "auth" and pending.get("keys_pruned"):
                            # The wave dropped the exhausted credential and kept
                            # going with the survivors, so this is not the run's
                            # end. Retry the batch that failed on the dead key
                            # rather than retiring it: it never had a fair attempt.
                            failures.pop(batch_id, None)
                            excluded.discard(batch_id)
                            continue
                        state["status"] = kind
                        save()
                        return state
                excluded = dependent_exclusions(campaign, excluded)
                state["deferred_batches"] = sorted(excluded)
                state["provider_failure_counts"] = failures
                state["last_recovery"] = [
                    {
                        "batch_id": i["batch_id"],
                        "restoration": i.get("restoration"),
                        "restoration_check": i.get("restoration_check"),
                    }
                    for i in pending.get("items", [])
                    if i.get("safe_to_continue")
                ]
                reason = pending.get("stop_reason")
                pending = None
                state.pop("active_wave_path", None)
                if reason in {"stop_file", "source_changed"} or str(reason).startswith("signal_"):
                    state["status"] = reason
                    break
                if provider_failed:
                    retry_streak = 1 if accepted else retry_streak + 1
                    wait(
                        "provider_cooldown",
                        min(1200, 300 * 2 ** min(retry_streak - 1, 2)),
                    )
                    continue
                retry_streak = 0
                if str(reason).startswith("controller_error"):
                    wait("waiting_after_controller_error", 120)
                    continue
                if reason == "no_eligible_unseen_items" and not accepted:
                    wait("waiting_for_eligible_work", 300)
                    continue
            if now() >= deadline or stop.exists():
                break
            try:
                quota = read_quota_budget(options.budget)
                state["quota"] = {
                    k: quota.get(k)
                    for k in (
                        "limit_quota",
                        "charges_quota",
                        "held_quota",
                        "unknown_hold_quota",
                        "remaining_quota",
                        "halt_reason",
                    )
                }
                if quota.get("halt_reason"):
                    state["status"] = "quota_halted"
                    break
                if quota["remaining_quota"] < scale["minimum_request_quota"](options.quote):
                    state["status"] = "quota_exhausted"
                    break
                state["status"] = "checking_remote"
                save()
                health = dict(scale["remote_warmup_check"]())
                state["remote_warmup"] = (state["remote_warmup"] + [health])[-20:]
                if not health.get("available") or not health.get("ready_for_checks", True):
                    wait("waiting_for_remote", 120)
                    continue
            except (
                OSError,
                RuntimeError,
                ValueError,
                TimeoutError,
                subprocess.SubprocessError,
            ) as exc:
                state["health_error"] = {
                    "type": type(exc).__name__,
                    "message": str(exc)[:500],
                }
                wait("waiting_for_services", 120)
                continue
            if now() >= deadline or stop.exists():
                break
            wave = SimpleNamespace(
                project=project,
                campaign=campaign,
                workers=workers,
                handoff_limit=workers,
                stage="mixed",
                continuous=True,
                on_wave_created=wave_created,
                max_items=1035,
                # Dispatch for the whole remaining run, not for one child budget.
                # The wave already waits for in-flight children to drain, so a
                # shorter window buys nothing and costs the idle slots of the
                # drain itself: with the window pinned to the four-hour child
                # budget, the 2026-10-06 run dispatched for 5.7h, 4.0h and 14h in
                # three waves while the deadline was twenty hours out, and every
                # window that closed early left its free slots empty until the
                # slowest child finished. The deadline is the real bound; the
                # wave's own fuse, quota and stop-file checks still run inside.
                max_wall=max(30, (deadline - now()) / 60),
                quota_limit=quota["limit_quota"],
                quota_budget=options.budget,
                quote=options.quote,
                ignore_unknown_holds=False,
                no_infrastructure_fuse=False,
                excluded_batches=tuple(sorted(excluded)),
                supervisor_stop_file=stop,
            )
            state["status"] = "running"
            state.pop("resume_at_utc", None)
            save()
            pending = scale["execute"](wave)
            state["waves"].append(
                {
                    k: pending.get(k)
                    for k in (
                        "run_dir",
                        "started_at",
                        "finished_at",
                        "stop_reason",
                        "before",
                        "after",
                        "quota",
                    )
                }
            )
            save()
        if stop.exists():
            state["status"] = "stop_file"
        elif now() >= deadline:
            state["status"] = "wall_limit"
    finally:
        for sig, handler in handlers.items():
            signal.signal(sig, handler)
        state["finished_at"] = datetime.fromtimestamp(now(), UTC).isoformat()
        save()
    return state
