"""Replay long outages, task recovery, exhaustion and STOP without paid calls."""

import json
from types import SimpleNamespace

from leanflow_cli.formalization import campaign_supervision as supervisor


def setup(tmp_path, monkeypatch):
    clock = [0.0]
    campaign = tmp_path / "fate-x-work/HDP/Environments/campaign.json"
    campaign.parent.mkdir(parents=True)
    campaign.write_text(json.dumps({"batches": [{"id": "a", "labels": ["A"]}]}))
    options = SimpleNamespace(
        log_dir=tmp_path / "logs",
        hours=8,
        defer_batch=[],
        budget=tmp_path / "budget.json",
        quote=tmp_path / "quote.json",
    )
    quota = {
        "limit_quota": 10000000,
        "remaining_quota": 8450074,
        "unknown_hold_quota": 1185041,
    }
    monkeypatch.setattr(supervisor, "read_quota_budget", lambda p: dict(quota))
    scale = {
        "source_hashes": lambda: {"x": "same"},
        "minimum_request_quota": lambda p: 107731,
        "remote_warmup_check": lambda: {"available": True, "ready_for_checks": True},
        "recover_continuous_wave": lambda *a: True,
    }
    return clock, options, quota, scale


def run(clock, options, scale, tmp_path, pause=None):
    return supervisor.supervise_continuously(
        options,
        scale,
        root=tmp_path,
        now=lambda: clock[0],
        pause=pause or (lambda s: clock.__setitem__(0, clock[0] + s)),
    )


def wave(kind="infrastructure", reason="consecutive_infrastructure_failures"):
    return {
        "finished_at": "done",
        "active": {},
        "stop_reason": reason,
        "items": [
            {
                "batch_id": "a",
                "classification": kind,
                "stage": "statements",
                "new_attempts": [{"success": False}],
            }
        ],
    }


def test_eight_hours_of_provider_outage_keeps_waiting_but_caps_each_task(tmp_path, monkeypatch):
    clock, options, quota, scale = setup(tmp_path, monkeypatch)
    calls = []

    def execute(options):
        calls.append(options)
        if "a" in options.excluded_batches:
            return {
                "stop_reason": "no_eligible_unseen_items",
                "items": [],
                "active": {},
            }
        return wave()

    scale["execute"] = execute
    state = run(clock, options, scale, tmp_path)
    assert clock[0] == 8 * 3600
    assert state["status"] == "wall_limit"
    assert len([w for w in calls if "a" not in w.excluded_batches]) == 3
    assert state["deferred_batches"] == ["a"]
    assert quota["unknown_hold_quota"] == 1185041
    assert state["budget_extension_allowed"] is False


def test_remote_outage_waits_then_recovers_without_paying_during_wait(tmp_path, monkeypatch):
    clock, options, quota, scale = setup(tmp_path, monkeypatch)
    health = []

    def warm():
        health.append(clock[0])
        if len(health) <= 4:
            return {"available": False}
        return {"available": True}

    scale["remote_warmup_check"] = warm

    def execute(w):
        assert clock[0] >= 480
        (options.log_dir / "STOP").touch()
        return wave("accepted")

    scale["execute"] = execute
    state = run(clock, options, scale, tmp_path)
    assert state["status"] == "stop_file"
    assert len(health) == 5


def test_pending_recovery_never_dispatches_until_restoration_succeeds(tmp_path, monkeypatch):
    clock, options, quota, scale = setup(tmp_path, monkeypatch)
    calls, recoveries = [], []

    def recover(result, *args):
        recoveries.append(clock[0])
        if len(recoveries) < 3:
            return False
        result["items"][0]["safe_to_continue"] = True
        return True

    def execute(w):
        calls.append(w)
        if len(calls) > 1:
            assert "a" in w.excluded_batches
            (options.log_dir / "STOP").touch()
        return wave(reason="task_recovery")

    scale.update(execute=execute, recover_continuous_wave=recover)
    state = run(clock, options, scale, tmp_path)
    assert len(calls) == 2
    assert recoveries == [0, 60, 120, 120]
    assert state["status"] == "stop_file"


def test_quota_exhaustion_blocks_before_any_dispatch(tmp_path, monkeypatch):
    clock, options, quota, scale = setup(tmp_path, monkeypatch)
    quota["remaining_quota"] = 100
    scale["execute"] = lambda w: (_ for _ in ()).throw(AssertionError("must not dispatch"))
    state = run(clock, options, scale, tmp_path)
    assert state["status"] == "quota_exhausted"
    assert state["waves"] == []


def test_checkpoint_restart_preserves_deadline_and_retry_history(tmp_path, monkeypatch):
    clock, options, quota, scale = setup(tmp_path, monkeypatch)
    scale["execute"] = lambda w: wave()

    def pause(delay):
        clock[0] += delay
        (options.log_dir / "STOP").touch()

    first = run(clock, options, scale, tmp_path, pause=pause)
    assert first["provider_failure_counts"] == {"a": 1}
    (options.log_dir / "STOP").unlink()
    clock[0] += 100

    def execute(w):
        (options.log_dir / "STOP").touch()
        return wave()

    scale["execute"] = execute
    second = run(clock, options, scale, tmp_path)
    assert second["deadline_utc"] == first["deadline_utc"]
    assert second["started_at"] == first["started_at"]
    assert second["provider_failure_counts"] == {"a": 2}


def _quota_wave(diagnostic):
    return {
        "finished_at": "done",
        "active": {},
        "stop_reason": "quota",
        "items": [
            {
                "batch_id": "a",
                "classification": "quota",
                "stage": "statements",
                "new_attempts": [{"success": False, "final_diagnostic": diagnostic}],
            }
        ],
    }


def test_an_expired_quote_is_reported_as_such_not_as_exhaustion(tmp_path, monkeypatch):
    """The run must not look like a spend problem when its quote simply aged out.

    The 2026-10-06 run stopped at 02:04:01 UTC with 128.7M of a 267.9M limit
    unspent: its quote was observed at 02:03:45 UTC the previous day, so it
    expired sixteen seconds before the stop. Recording that as ``quota`` sends an
    operator to top up a ledger that was never short.
    """
    clock, options, quota, scale = setup(tmp_path, monkeypatch)
    scale["execute"] = lambda w: _quota_wave(
        "provider quota guard: quote observation is expired or in the future"
    )
    state = run(clock, options, scale, tmp_path)
    assert state["status"] == "quote_expired"
    assert "expired" in state["quote_expired_diagnostic"]
    assert quota["remaining_quota"] == 8450074
