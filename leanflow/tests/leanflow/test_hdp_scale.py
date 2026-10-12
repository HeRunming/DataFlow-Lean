"""Exercise finite HDP scheduling without launching provider or Lean processes."""

from __future__ import annotations

import hashlib
import importlib.machinery
import importlib.util
import itertools
import json
import signal
import sys
from pathlib import Path
from types import SimpleNamespace

import pytest


@pytest.fixture
def scale(monkeypatch):
    path = Path(__file__).resolve().parents[2] / "hdp" / "hdp-scale"
    loader = importlib.machinery.SourceFileLoader("hdp_scale_test", str(path))
    spec = importlib.util.spec_from_loader(loader.name, loader)
    module = importlib.util.module_from_spec(spec)
    loader.exec_module(module)
    monkeypatch.setattr(module, "recovery_runtime_idle", lambda: {"checked": False})
    return module


def campaign(tmp_path, count=6):
    path = tmp_path / "campaign.json"
    source = tmp_path / "questions.json"
    source.write_text(
        json.dumps(
            [
                {
                    "label": str(n),
                    "question": f"For every natural n, n + {n} = {n} + n.",
                }
                for n in range(count)
            ]
        )
    )
    path.write_text(
        json.dumps(
            {
                "source": "questions.json",
                "spent_usd": 0,
                "budget_usd": 100,
                "batches": [
                    {
                        "id": f"i{n}",
                        "labels": [str(n)],
                        "status": "pending",
                        "attempts": [],
                    }
                    for n in range(count)
                ],
            }
        )
    )
    return path


def test_dry_preview_preserves_ledger_dependencies_and_complex_items(tmp_path, scale):
    path = campaign(tmp_path)
    data = json.loads(path.read_text())
    data["batches"][0]["source_complexity_tier"] = "complex"
    data["batches"][1]["dependency_labels"] = ["0"]
    data["batches"][2]["status"] = "statement_escalate"
    data["batches"][3]["lease"] = {
        "worker_id": "other",
        "expires_at": "2999-01-01T00:00:00+00:00",
    }
    path.write_text(json.dumps(data))
    before = path.read_bytes()
    result = scale.preview(path, tmp_path, {"i4"}, 6)
    assert {r["batch_id"] for r in result} == {"i0", "i5"}
    assert path.read_bytes() == before
    assert all(r["source_sha256"] for r in result)
    assert not (tmp_path / ".leanflow").exists()


def test_controller_lock_rejects_second_supervisor(tmp_path, scale):
    with scale.controller_lock(tmp_path):
        with pytest.raises(RuntimeError, match="another"):
            with scale.controller_lock(tmp_path):
                pytest.fail("duplicate controller acquired the lock")


def test_infrastructure_fuse_setting_records_cli_and_environment_origin(monkeypatch, scale):
    monkeypatch.delenv(scale.NO_INFRASTRUCTURE_FUSE_ENV, raising=False)
    assert scale.no_infrastructure_fuse_setting(False) == (False, "default")
    assert scale.no_infrastructure_fuse_setting(True) == (True, "cli")
    monkeypatch.setenv(scale.NO_INFRASTRUCTURE_FUSE_ENV, "yes")
    assert scale.no_infrastructure_fuse_setting(False) == (True, "env")
    assert scale.no_infrastructure_fuse_setting(True) == (True, "cli+env")
    monkeypatch.setenv(scale.NO_INFRASTRUCTURE_FUSE_ENV, "off")
    assert scale.no_infrastructure_fuse_setting(False) == (False, "default")


def test_key_pool_metadata_records_only_fingerprints(scale):
    metadata = scale.key_pool_metadata({"M2F_CODEX_API_KEYS": "alpha,beta,alpha"})
    assert metadata["key_pool_size"] == 3
    assert metadata["key_fingerprint_count"] == 2
    assert metadata["key_fingerprints"]
    assert all(len(value) == 64 for value in metadata["key_fingerprints"])
    assert "alpha" not in str(metadata)


def _fingerprint(value: str) -> str:
    return hashlib.sha256(value.encode()).hexdigest()


def test_resolve_key_pool_keeps_pool_order_and_drops_duplicates(scale):
    pool = scale.resolve_key_pool({"M2F_CODEX_API_KEYS": "one, two ,one\nthree"})
    # Order is load-bearing: HDP_WORKER_SLOT indexes into this list, so
    # reordering would silently rebind every worker to a different credential.
    assert pool == ["one", "two", "three"]


def test_prune_exhausted_keys_drops_only_the_key_that_reported_exhaustion(scale):
    env = {
        "M2F_CODEX_API_KEYS": "dead,alive1,alive2",
        "M2F_CODEX_API_KEY": "dead",
        "OPENAI_API_KEY": "dead",
    }
    item = {
        "batch_id": "items-3.12",
        "classification": "auth",
        "credential_sha256": _fingerprint("dead"),
        "new_attempts": [
            {
                "final_diagnostic": (
                    "Error code: 403 - token quota is not enough, " "token remain quota: 0.058035"
                )
            }
        ],
    }
    pruned, audits = scale.prune_exhausted_keys(env, [item])
    assert pruned["M2F_CODEX_API_KEYS"] == "alive1,alive2"
    # The single-key aliases back the no-slot child path, so they must not name
    # the dead credential any more.
    assert pruned["M2F_CODEX_API_KEY"] == "alive1"
    assert pruned["OPENAI_API_KEY"] == "alive1"
    assert audits == [
        {
            "fingerprint": _fingerprint("dead"),
            "diagnostic": item["new_attempts"][0]["final_diagnostic"],
            "pool_before": 3,
            "pool_after": 2,
        }
    ]
    # The caller's mapping is never mutated in place.
    assert env["M2F_CODEX_API_KEYS"] == "dead,alive1,alive2"


def test_prune_exhausted_keys_ignores_a_generic_403(scale):
    """A 403 that does not name a key or balance problem says nothing about the pool."""
    env = {"M2F_CODEX_API_KEYS": "one,two"}
    item = {
        "batch_id": "items-3.12",
        "classification": "auth",
        "credential_sha256": _fingerprint("one"),
        "new_attempts": [{"final_diagnostic": "Error code: 403 - forbidden route"}],
    }
    pruned, audits = scale.prune_exhausted_keys(env, [item])
    assert pruned is env
    assert audits == []


def test_prune_exhausted_keys_stops_when_every_key_is_gone(scale):
    """With no survivors the pool is left intact so the run halts instead."""
    env = {"M2F_CODEX_API_KEYS": "one,two"}
    items = [
        {
            "batch_id": f"items-{index}",
            "classification": "auth",
            "credential_sha256": _fingerprint(name),
            "new_attempts": [{"final_diagnostic": "token quota is not enough"}],
        }
        for index, name in enumerate(("one", "two"))
    ]
    pruned, audits = scale.prune_exhausted_keys(env, items)
    assert pruned is env
    assert audits == []


def test_infrastructure_fuse_bypass_continues_dispatch_without_repeating_items(
    tmp_path, monkeypatch, scale
):
    path = campaign(tmp_path, 8)
    # Pin the threshold to the streak this test actually reaches, so the test
    # exercises the bypass mechanism rather than the shipped constant's value.
    monkeypatch.setattr(scale, "INFRASTRUCTURE_FUSE_THRESHOLD", 2)
    options = SimpleNamespace(
        project=tmp_path,
        campaign=path,
        workers=2,
        max_items=4,
        max_wall=180,
        quota_limit=2_000_000,
        quote=tmp_path / "quote.json",
        no_infrastructure_fuse=True,
        no_infrastructure_fuse_source="test",
    )
    monkeypatch.setattr(scale, "quota_environment", lambda *args: {})
    monkeypatch.setattr(scale, "quota_status", lambda env: {"remaining_quota": 1_000_000})
    created = []

    class FakeProcess:
        def __init__(self, command, **kwargs):
            self.batch_id = command[command.index("--batch-id") + 1]
            self.pid = len(created) + 100
            self.log_path = Path(kwargs["stdout"].name)
            self.finished = False
            created.append(self)

        def poll(self):
            if not self.finished:
                data = json.loads(path.read_text())
                batch = next(b for b in data["batches"] if b["id"] == self.batch_id)
                attempt = {
                    "stage": "statements",
                    "success": False,
                    "worker_id": f"worker-{self.pid}",
                    "failure_class": "infrastructure",
                    "infrastructure_failure": True,
                }
                batch["attempts"].append(attempt)
                batch["last_outcome"] = attempt
                batch["status"] = "statement_retry"
                path.write_text(json.dumps(data))
                self.log_path.write_text(
                    json.dumps(
                        {
                            "batch_id": self.batch_id,
                            "stage": "statements",
                            "outcome": attempt,
                        }
                    )
                    + "\n"
                )
                self.finished = True
            return 2

    clock = iter(range(1000))
    result = scale.execute(
        options,
        popen=FakeProcess,
        clock=lambda: next(clock),
        pause=lambda _seconds: None,
    )
    assert result["stop_reason"] == "item_limit"
    assert result["no_infrastructure_fuse"] is True
    assert result["no_infrastructure_fuse_source"] == "test"
    assert len(created) == 4
    assert len({item.batch_id for item in created}) == 4
    events = [
        json.loads(line)
        for line in (next((tmp_path / ".leanflow/scale-runs").iterdir()) / "events.jsonl")
        .read_text()
        .splitlines()
    ]
    assert any(event["event"] == "infrastructure_fuse_bypassed" for event in events)


@pytest.mark.parametrize("failure", ["accepted", "infrastructure", "auth", "quota", "rate_limit"])
def test_finite_controller_drains_and_never_repeats_an_item(tmp_path, monkeypatch, scale, failure):
    path = campaign(tmp_path, 10)
    # Pin the threshold to 2 so the infrastructure case stops after the same
    # number of launches this test budgets for; the shipped constant is a
    # tuning value and asserting against it here would make the test brittle.
    monkeypatch.setattr(scale, "INFRASTRUCTURE_FUSE_THRESHOLD", 2)
    options = SimpleNamespace(
        project=tmp_path,
        campaign=path,
        workers=4,
        max_items=6,
        max_wall=180,
        quota_limit=2_000_000,
        quote=tmp_path / "quote.json",
    )
    monkeypatch.setattr(scale, "quota_environment", lambda *args: {})
    monkeypatch.setattr(scale, "quota_status", lambda env: {"remaining_quota": 1_000_000})
    created = []

    class FakeProcess:
        def __init__(self, command, **kwargs):
            self.batch_id = command[command.index("--batch-id") + 1]
            self.pid = len(created) + 100
            self.finished = False
            self.log_path = Path(kwargs["stdout"].name)
            created.append(self)
            assert command[command.index("--lean-slots") + 1] == "1"
            assert command[command.index("--statement-candidates") + 1] == "1"
            assert "--batch-item-limit" not in command

        def poll(self):
            if not self.finished:
                data = json.loads(path.read_text())
                batch = next(b for b in data["batches"] if b["id"] == self.batch_id)
                attempt = {
                    "stage": "statements",
                    "success": failure == "accepted",
                    "worker_id": f"worker-{self.pid}",
                    "reason": {
                        "auth": "401 Unauthorized",
                        "quota": "quota exceeded",
                        "rate_limit": "429 too many requests",
                    }.get(failure, ""),
                    "infrastructure_failure": failure == "infrastructure",
                }
                batch["attempts"].append(attempt)
                batch["last_outcome"] = attempt
                batch["status"] = (
                    "statements_completed" if failure == "accepted" else "statement_retry"
                )
                path.write_text(json.dumps(data))
                self.log_path.write_text(
                    json.dumps(
                        {
                            "batch_id": self.batch_id,
                            "stage": "statements",
                            "outcome": attempt,
                        }
                    )
                    + "\n"
                )
                self.finished = True
            return 0 if failure == "accepted" else 2

    clock = iter(range(1000))
    result = scale.execute(
        options, popen=FakeProcess, clock=lambda: next(clock), pause=lambda _: None
    )
    # A failure burst pauses dispatch for a cooldown but no longer ends the wave,
    # so an all-infrastructure run keeps refilling its slots until a real limit
    # (here max_items) is reached -- exactly like an accepted run. Ending the
    # wave on the fuse is what left four slots idle for 11.5 hours on 2026-10-04.
    # auth and quota stay terminal: they need an operator, not a cooldown.
    # rate_limit pauses and refills too (2026-10-12): this relay's 429 is a
    # per-account concurrency cap that clears in seconds, and treating it as
    # terminal idled half the slots for hours in three consecutive runs.
    assert len(created) == (6 if failure in {"accepted", "infrastructure", "rate_limit"} else 4)
    assert len({p.batch_id for p in created}) == len(created)
    assert all(p.finished for p in created)
    assert result["active"] == {}
    assert (
        result["stop_reason"]
        == {
            "accepted": "item_limit",
            "infrastructure": "item_limit",
            "auth": "auth",
            "quota": "quota",
            "rate_limit": "item_limit",
        }[failure]
    )
    run_dir = next((tmp_path / ".leanflow/scale-runs").iterdir())
    # The before/after snapshots are opt-in: they have no code consumer and were
    # ~99% of the scale-runs tree, so the default run must not write them.
    assert not (run_dir / "campaign-before.json").exists()
    assert not (run_dir / "campaign-after.json").exists()
    assert (run_dir / "events.jsonl").is_file()
    assert all(Path(item["log"]).is_file() for item in result["items"])


def test_campaign_snapshots_are_opt_in(tmp_path, monkeypatch, scale):
    """A run that asks for the rollback snapshots still gets them."""
    path = campaign(tmp_path, 10)
    monkeypatch.setenv(scale.CAMPAIGN_SNAPSHOTS_ENV, "1")
    options = SimpleNamespace(
        project=tmp_path,
        campaign=path,
        workers=1,
        max_items=1,
        max_wall=180,
        quota_limit=2_000_000,
        quote=tmp_path / "quote.json",
    )
    monkeypatch.setattr(scale, "quota_environment", lambda *args: {})
    monkeypatch.setattr(scale, "quota_status", lambda env: {"remaining_quota": 1_000_000})
    created = []

    class FakeProcess:
        def __init__(self, command, **kwargs):
            self.batch_id = command[command.index("--batch-id") + 1]
            self.pid = len(created) + 100
            self.finished = False
            self.log_path = Path(kwargs["stdout"].name)
            created.append(self)

        def poll(self):
            if not self.finished:
                data = json.loads(path.read_text())
                batch = next(b for b in data["batches"] if b["id"] == self.batch_id)
                attempt = {
                    "stage": "statements",
                    "success": True,
                    "worker_id": f"worker-{self.pid}",
                }
                batch["attempts"].append(attempt)
                batch["last_outcome"] = attempt
                batch["status"] = "statements_completed"
                path.write_text(json.dumps(data))
                self.log_path.write_text(
                    json.dumps(
                        {"batch_id": self.batch_id, "stage": "statements", "outcome": attempt}
                    )
                    + "\n"
                )
                self.finished = True
            return 0

    clock = iter(range(1000))
    scale.execute(options, popen=FakeProcess, clock=lambda: next(clock), pause=lambda _: None)
    run_dir = next((tmp_path / ".leanflow/scale-runs").iterdir())
    assert (run_dir / "campaign-before.json").is_file()
    assert (run_dir / "campaign-after.json").is_file()


def test_forbidden_format_diagnostic_is_semantic_not_auth(scale):
    assert (
        scale.failure_kind(
            [
                {
                    "success": False,
                    "failure_stage": "format_check",
                    "final_diagnostic": "draft contains forbidden statement-lane token: opaque",
                }
            ],
            1,
        )
        == "semantic"
    )


def test_old_failure_is_not_reused_as_new_success(scale):
    assert scale.failure_kind([], 0) == "infrastructure"
    assert (
        scale.failure_kind([{"success": False, "failure_class": "semantic_review_block"}], 2)
        == "semantic"
    )


def test_sigterm_child_persists_aborted_attempt_before_lease_release(tmp_path, monkeypatch, scale):
    path = campaign(tmp_path, count=1)
    options = SimpleNamespace(
        project=tmp_path,
        campaign=path,
        workers=1,
        max_items=1,
        max_wall=45,
        quota_limit=2_000_000,
        quote=tmp_path / "quote.json",
    )
    monkeypatch.setattr(scale, "quota_environment", lambda *args: {})
    monkeypatch.setattr(scale, "quota_status", lambda env: {"remaining_quota": 1_000_000})

    class TerminatedProcess:
        pid = 999

        def poll(self):
            return -signal.SIGTERM

    def launch(*args, **kwargs):
        data = json.loads(path.read_text())
        data["batches"][0]["lease"] = {
            "worker_id": "worker-test",
            "expires_at": "2999-01-01T00:00:00+00:00",
        }
        path.write_text(json.dumps(data))
        return TerminatedProcess()

    result = scale.execute(
        options,
        popen=launch,
        clock=itertools.repeat(0).__next__,
        pause=lambda _seconds: None,
    )
    assert result["items"][0]["classification"] == "infrastructure"
    persisted = json.loads(path.read_text())
    batch = persisted["batches"][0]
    assert "lease" not in batch
    attempt = batch["attempts"][-1]
    assert attempt["failure_class"] == "infrastructure"
    assert attempt["aborted"] is True
    assert attempt["inflight"] is True
    assert attempt["interruption_kind"] == "aborted"
    assert attempt["recovery_receipt"]["kind"] == "campaign_interruption"


def test_quote_required_before_any_paid_child(tmp_path, scale):
    path = campaign(tmp_path)
    options = SimpleNamespace(
        project=tmp_path,
        campaign=path,
        workers=4,
        max_items=6,
        max_wall=180,
        quota_limit=100,
        quote=tmp_path / "missing.json",
    )
    with pytest.raises(ValueError, match="quote"):
        scale.execute(options, popen=lambda *a, **k: pytest.fail("must not launch"))


def test_stop_file_prevents_dispatch(tmp_path, monkeypatch, scale):
    path = campaign(tmp_path)
    options = SimpleNamespace(
        project=tmp_path,
        campaign=path,
        workers=4,
        max_items=6,
        max_wall=180,
        quota_limit=100,
        quote=tmp_path / "unused.json",
    )

    def quota_environment(_options, run_dir):
        (run_dir / "STOP").touch()
        return {}

    monkeypatch.setattr(scale, "quota_environment", quota_environment)
    monkeypatch.setattr(scale, "quota_status", lambda env: {"remaining_quota": 100})
    result = scale.execute(options, popen=lambda *a, **k: pytest.fail("STOP must prevent launch"))
    assert result["stop_reason"] == "stop_file"
    assert result["items"] == []


def test_receipts_require_new_stage_and_matching_worker(tmp_path, scale):
    log = tmp_path / "item.log"
    log.write_text(
        json.dumps({"stage": "statements", "batch_id": "i0", "outcome": {"worker_id": "owner"}})
    )
    item = {"batch_id": "i0", "log": str(log), "attempts_before": 1}
    batch = {
        "attempts": [
            {"worker_id": "owner", "stage": "statements", "success": True},
            {"worker_id": "other", "stage": "statements", "success": True},
            {"worker_id": "owner", "stage": "proofs", "success": True},
        ]
    }
    assert scale.item_receipts(item, batch) == []


@pytest.mark.parametrize("stage", ["statements", "proofs"])
def test_receipts_accept_top_level_identity_without_borrowing(tmp_path, scale, stage):
    log = tmp_path / "item.log"
    log.write_text(json.dumps({"stage": stage, "batch_id": "i0", "worker_id": "owner"}))
    item = {"batch_id": "i0", "stage": stage, "log": str(log), "attempts_before": 1}
    receipt = {"worker_id": "owner", "stage": stage, "success": True}
    batch = {"attempts": [receipt, {**receipt, "worker_id": "other"}, receipt]}
    assert scale.item_receipts(item, batch) == [receipt]
    assert item["worker_id"] == "owner"
    log.write_text(json.dumps({"stage": stage, "batch_id": "other", "worker_id": "owner"}))
    assert scale.item_receipts(item, batch) == []


def recovery_case(tmp_path, scale):
    target = tmp_path / "Main.lean"
    target.write_text("theorem demo : True := by sorry\n")
    item = {
        "stage": "proofs",
        "batch_id": "b",
        "worker_id": "w",
        "target_path": str(target),
        "recovery_source_before": scale.recovery_snapshot(str(target)),
        "attempts_before_sha256": scale.digest(b"[]"),
        "recovery_runtime": {"checked": True, "local_idle": True, "remote_idle": True},
        "child_result": {
            "stage": "proofs",
            "batch_id": "b",
            "worker_id": "w",
            "exit_code": 124,
            "success": False,
        },
    }
    return item, {"attempts": []}, target


def test_timeout_defers_only_after_runtime_source_and_ledger_checks(tmp_path, scale):
    item, batch, _target = recovery_case(tmp_path, scale)
    result = scale._missing_receipt_recovery(item, batch, 1)
    assert result["safe_to_retry"] is True
    assert result["disposition"] == "defer_for_this_run"


@pytest.mark.parametrize(
    "bad",
    [
        "target",
        "helper",
        "lease",
        "attempt",
        "owner",
        "runtime",
        "missing",
        "unknown_exit",
    ],
)
def test_recovery_rejects_incomplete_or_changed_evidence(tmp_path, scale, bad):
    item, batch, target = recovery_case(tmp_path, scale)
    if bad == "target":
        target.write_text("theorem demo : False := by sorry\n")
    elif bad == "helper":
        target.with_name("Helper.lean").write_text("axiom boom : False\n")
    elif bad == "lease":
        batch["lease"] = {"worker_id": "other"}
    elif bad == "attempt":
        batch["attempts"] = [{"success": True}]
    elif bad == "owner":
        item["child_result"]["worker_id"] = "other"
    elif bad == "runtime":
        item["recovery_runtime"]["remote_idle"] = False
    elif bad == "missing":
        target.unlink()
    else:
        item["child_result"]["exit_code"] = 2
    assert not scale._missing_receipt_recovery(item, batch, 1)["safe_to_retry"]


def test_missing_before_snapshot_never_means_unchanged(tmp_path, scale):
    item, batch, target = recovery_case(tmp_path, scale)
    item["recovery_source_before"] = None
    target.unlink()
    assert not scale._missing_receipt_recovery(item, batch, 1)["safe_to_retry"]


@pytest.mark.parametrize("busy", ["local", "remote", "unavailable", "none"])
def test_runtime_probe_detects_orphans_without_exposing_commands(scale, busy):
    def run(argv, **kwargs):
        if busy == "unavailable":
            raise OSError("unavailable")
        if argv[0] == "ps":
            text = (
                "123 python -m leanflow_cli.native.native_runner"
                if busy == "local"
                else "1 hdp-long-run"
            )
        else:
            text = json.dumps({"checked": True, "busy_pids": [123] if busy == "remote" else []})
        return SimpleNamespace(stdout=text)

    # Load the real callable independently of the fixture's network guard.
    import runpy

    real = runpy.run_path(str(Path(__file__).resolve().parents[2] / "hdp" / "hdp-scale"))
    status = real["recovery_runtime_idle"](run=run)
    assert all(status.get(k) for k in ("checked", "local_idle", "remote_idle")) == (busy == "none")


def test_import_halted_quota_budget_preserves_charges_and_records_ack(tmp_path, scale):
    source = tmp_path / "old-quota.json"
    destination = tmp_path / "scale-budget.json"
    source.write_text(
        json.dumps(
            {
                "version": 1,
                "unit": "provider_quota",
                "limit_quota": 2_000_000,
                "charges_quota": 147_059,
                "reservations": {},
                "halt_reason": "reported usage exceeded conservative reservation",
            }
        )
    )
    imported = scale.import_halted_quota_budget(source, destination)
    assert imported["charges_quota"] == 147_059
    assert imported["remaining_quota"] == 1_852_941
    assert imported["imported_from_sha256"]
    assert imported["import_acknowledged_at"]
    assert "halt_reason" not in imported
    assert "halt_reason" in json.loads(source.read_text())
    with pytest.raises(RuntimeError, match="already exists"):
        scale.import_halted_quota_budget(source, destination)


def _requires_live_workspace(scale):
    """Skip a test that reads a real HDP deployment's logs or campaign state.

    Those artifacts are private run state and are not part of the published
    tree; the tests remain useful against a real workspace.
    """
    if not (scale.WORKSPACE / ".leanflow-home").is_dir():
        pytest.skip("needs a live HDP workspace (set HDP_WORKSPACE)")


def test_quote_validation_requires_current_input_and_output_allowances(
    scale, tmp_path, monkeypatch
):
    _requires_live_workspace(scale)
    # The pinned relay is plain HTTP; quoting it needs the explicit opt-in.
    monkeypatch.setenv("LEANFLOW_ALLOW_INSECURE_QUOTA_ENDPOINT", "1")
    quote_root = scale.WORKSPACE / ".leanflow-home/logs/zcloud-pricing-20260909T091106Z"
    candidates = sorted(quote_root.glob("quota-quote-wave5-*.json"))
    current = candidates[-1] if candidates else quote_root / "quota-quote.json"
    from datetime import UTC, datetime

    payload = json.loads(current.read_text())
    payload["observed_at_utc"] = datetime.now(UTC).isoformat()
    # The archived fixture is a zcloud-era quote; rebase it onto whatever pair
    # hdp-scale is pinned to now, so this test checks the allowance rule rather
    # than which provider happened to be current when the fixture was captured.
    payload["base_url"] = scale.PINNED_PROVIDER_BASE_URL
    payload["model"] = scale.PINNED_PROVIDER_MODEL
    fixture = tmp_path / "quote.json"
    fixture.write_text(json.dumps(payload))
    contents, metadata = scale.verified_quote_snapshot(fixture)
    assert len(contents) > 100
    assert metadata["provider_input_allowance_tokens"] >= 16_384
    assert metadata["provider_output_allowance_tokens"] >= 16_384


def test_quote_validation_rejects_a_quote_for_another_provider(scale, tmp_path, monkeypatch):
    """A quote fetched from one endpoint cannot price calls made to another."""
    _requires_live_workspace(scale)
    monkeypatch.setenv("LEANFLOW_ALLOW_INSECURE_QUOTA_ENDPOINT", "1")
    quote_root = scale.WORKSPACE / ".leanflow-home/logs/zcloud-pricing-20260909T091106Z"
    candidates = sorted(quote_root.glob("quota-quote-wave5-*.json"))
    current = candidates[-1] if candidates else quote_root / "quota-quote.json"
    from datetime import UTC, datetime

    payload = json.loads(current.read_text())
    payload["observed_at_utc"] = datetime.now(UTC).isoformat()
    payload["base_url"] = "https://api.zcloudapi.com/v1"
    payload["model"] = "gpt-6-astra"
    fixture = tmp_path / "quote.json"
    fixture.write_text(json.dumps(payload))
    with pytest.raises(RuntimeError, match="fixed HDP provider and model"):
        scale.verified_quote_snapshot(fixture)


def test_quote_validation_rejects_outdated_run_snapshot(tmp_path, scale):
    _requires_live_workspace(scale)
    old = scale.WORKSPACE / "fate-x-work/.leanflow/scale-runs/20260909T132940Z/quota-quote.json"
    with pytest.raises(ValueError, match="quote observation|provider_output_allowance_tokens"):
        scale.verified_quote_snapshot(old)


def test_proof_preview_requires_existing_target_and_leases_ready_batch(tmp_path, scale):
    path = campaign(tmp_path, count=2)
    target = tmp_path / "Generated.lean"
    target.write_text("theorem demo : True := by sorry\n")
    (tmp_path / "FateXWork.lean").write_text("import Generated\n")
    data = json.loads(path.read_text())
    data["batches"][0].update(
        {
            "status": "statements_completed",
            "last_outcome": {"target_file": "Generated.lean"},
        }
    )
    data["batches"][1].update(
        {
            "status": "statements_completed",
            "last_outcome": {"target_file": "missing.lean"},
        }
    )
    path.write_text(json.dumps(data))
    planned = scale.preview(path, tmp_path, set(), 4, stage="proofs")
    assert [item["batch_id"] for item in planned] == ["i0"]
    assert planned[0]["stage"] == "proofs"
    assert planned[0]["target_file"] == "Generated.lean"
    assert planned[0]["target_check"]["eligible"] is True


def test_proof_target_inspection_rejects_shell_complete_and_unreachable(tmp_path, scale):
    shell = tmp_path / "Shell.lean"
    shell.write_text("import Mathlib\n")
    assert scale.inspect_proof_target(tmp_path, "Shell.lean")["reason"] == "empty_import_shell"

    complete = tmp_path / "Complete.lean"
    complete.write_text("theorem done : True := by trivial\n")
    (tmp_path / "FateXWork.lean").write_text("import Complete\n")
    assert scale.inspect_proof_target(tmp_path, "Complete.lean")["reason"] == "no_proof_placeholder"
    retry = scale.inspect_proof_target(tmp_path, "Complete.lean", allow_proof_retry=True)
    assert retry["explicit_proof_retry"] is True
    assert retry["eligible"] is True

    unreachable = tmp_path / "Pending.lean"
    unreachable.write_text("theorem pending : True := by sorry\n")
    check = scale.inspect_proof_target(tmp_path, "Pending.lean")
    assert check["has_declaration"] is True
    assert check["has_placeholder"] is True
    assert check["root_reachable"] is False
    assert check["reason"] == "root_unreachable"


def test_mixed_preview_balances_and_refills_active_lanes(tmp_path, scale):
    path = campaign(tmp_path, count=6)
    data = json.loads(path.read_text())
    for n in range(3):
        target = tmp_path / f"Generated{n}.lean"
        target.write_text(f"theorem demo{n} : True := by sorry\n")
        data["batches"][n].update(
            status="statements_completed",
            last_outcome={"target_file": target.name},
        )
    (tmp_path / "FateXWork.lean").write_text("\n".join(f"import Generated{n}" for n in range(3)))
    path.write_text(json.dumps(data))
    before = path.read_bytes()
    initial = scale.preview(path, tmp_path, set(), 4, stage="mixed")
    assert [r["stage"] for r in initial] == ["proofs", "statements"] * 2
    assert len({r["batch_id"] for r in initial}) == 4
    refill = scale.preview(
        path,
        tmp_path,
        {r["batch_id"] for r in initial},
        2,
        stage="mixed",
        active_stages=("proofs", "proofs"),
    )
    assert [r["stage"] for r in refill] == ["statements", "proofs"]
    assert path.read_bytes() == before


def test_proof_command_uses_explicit_proof_stage(scale):
    command = scale.command(Path("campaign.json"), "i0", stage="proofs")
    assert "--stage" in command
    assert command[command.index("--stage") + 1] == "proofs"
    assert "--bounded-statements" not in command


def test_cli_dry_run_propagates_proof_stage(monkeypatch, scale, capsys):
    _requires_live_workspace(scale)
    observed = {}

    def fake_preview(*args, **kwargs):
        observed["stage"] = kwargs.get("stage")
        return [{"stage": kwargs.get("stage")}]

    monkeypatch.setattr(scale, "preview", fake_preview)
    monkeypatch.setattr(sys, "argv", ["hdp-scale", "--stage", "proofs", "--max-items", "1"])
    assert scale.main() == 0
    payload = json.loads(capsys.readouterr().out)
    assert observed["stage"] == "proofs"
    assert payload["stage"] == "proofs"
    assert payload["items"] == [{"stage": "proofs"}]


def _isolated_source(path):
    path.write_text(
        json.dumps(
            {
                "version": 1,
                "unit": "provider_quota",
                "limit_quota": 2_000_000,
                "charges_quota": 438_498,
                "reservations": {
                    "charged-1": {"status": "charged", "reserved_quota": 10},
                    "unknown-1": {"status": "unknown", "reserved_quota": 66_114},
                },
                "halt_reason": "reported usage exceeded conservative reservation",
            }
        )
    )


def test_create_isolated_operator_budget_starts_clean_and_links_wave3(tmp_path, scale):
    source = tmp_path / "wave3.json"
    destination = tmp_path / "wave4.json"
    _isolated_source(source)
    before = source.read_bytes()
    quote_metadata = {
        "sha256": "quote-sha",
        "base_url": "https://api.zcloudapi.com/v1",
        "model": "gpt-6-astra",
        "pricing_version": "pricing-sha",
        "provider_input_allowance_tokens": 16_384,
        "provider_output_allowance_tokens": 16_384,
    }
    created = scale.create_isolated_operator_budget(
        source,
        destination,
        limit_quota=3_000_000,
        authorization_ref="wave4-approval-2026-09-10",
        authorized_at="2026-09-10T08:00:00+00:00",
        quote_metadata=quote_metadata,
    )
    assert source.read_bytes() == before
    assert created["charges_quota"] == 0
    assert created["held_quota"] == 0
    assert created["remaining_quota"] == 3_000_000
    assert created["reservations"] == {}
    assert created["operator_authorization"]["reference"] == "wave4-approval-2026-09-10"
    assert created["operator_authorization"]["authorized_at_utc"] == "2026-09-10T08:00:00+00:00"
    assert created["operator_authorization"]["raw_quota_limit_source"] == (
        "operator_authorized_new_provider_quota"
    )
    linkage = created["isolated_from"]
    assert linkage["wave"] == "wave3"
    assert linkage["source_sha256"] == scale.digest(before)
    assert linkage["source_summary"]["charges_quota"] == 438_498
    assert linkage["source_summary"]["held_quota"] == 66_114
    assert linkage["source_summary"]["unknown_hold_quota"] == 66_114
    assert linkage["source_summary"]["reservation_status_counts"] == {
        "charged": 1,
        "unknown": 1,
    }
    assert created["provider_quota_evidence"] == quote_metadata


def test_create_isolated_operator_budget_rejects_collision_and_same_path(tmp_path, scale):
    source = tmp_path / "wave3.json"
    destination = tmp_path / "wave4.json"
    _isolated_source(source)
    kwargs = {
        "limit_quota": 100,
        "authorization_ref": "approval",
        "authorized_at": "2026-09-10T08:00:00+00:00",
        "quote_metadata": {"sha256": "quote-sha"},
    }
    with pytest.raises(RuntimeError, match="must not replace"):
        scale.create_isolated_operator_budget(source, source, **kwargs)
    destination.write_text("{}")
    with pytest.raises(RuntimeError, match="already exists"):
        scale.create_isolated_operator_budget(source, destination, **kwargs)


@pytest.mark.parametrize(
    "authorized_at, message",
    [
        ("2026-09-10T08:00:00", "include a timezone"),
        ("not-a-time", "ISO-8601"),
        ("2999-01-01T00:00:00+00:00", "future"),
    ],
)
def test_create_isolated_operator_budget_rejects_invalid_authorization_time(
    tmp_path, scale, authorized_at, message
):
    source = tmp_path / "wave3.json"
    _isolated_source(source)
    with pytest.raises(ValueError, match=message):
        scale.create_isolated_operator_budget(
            source,
            tmp_path / "wave4.json",
            limit_quota=100,
            authorization_ref="approval",
            authorized_at=authorized_at,
            quote_metadata={},
        )


def test_continuous_controller_snapshots_failed_proof_before_recovery(tmp_path, monkeypatch, scale):
    from leanflow_cli.formalization.campaign_recovery import reconcile_wave

    path = campaign(tmp_path, 1)
    target = tmp_path / "Book" / "Batch" / "Main.lean"
    target.parent.mkdir(parents=True)
    target.write_text("theorem demo : True := by sorry\n")
    original = target.read_bytes()
    options = SimpleNamespace(
        project=tmp_path,
        campaign=path,
        workers=1,
        max_items=3,
        max_wall=180,
        quota_limit=2000000,
        quote=tmp_path / "q.json",
        continuous=True,
        stage="proofs",
    )
    monkeypatch.setattr(scale, "quota_environment", lambda *a: {})
    monkeypatch.setattr(scale, "quota_status", lambda env: {"remaining_quota": 1000000})
    monkeypatch.setattr(
        scale,
        "preview",
        lambda *a, **k: [
            {
                "batch_id": "i0",
                "stage": "proofs",
                "target_file": str(target.relative_to(tmp_path)),
                "attempts_before": 0,
            }
        ],
    )

    class Child:
        pid = 123456789

        def __init__(self, command, **kwargs):
            target.write_text("unverified modified candidate")
            Path(kwargs["stdout"].name).write_text(
                json.dumps(
                    {
                        "batch_id": "i0",
                        "stage": "proofs",
                        "worker_id": "worker",
                        "success": False,
                        "exit_code": 124,
                    }
                )
            )

        def poll(self):
            return 1

    clock = iter(range(1000))
    state = scale.execute(options, popen=Child, clock=lambda: next(clock), pause=lambda _: None)
    assert state["stop_reason"] == "task_recovery"
    assert len(state["items"]) == 1
    assert Path(state["items"][0]["proof_snapshot"]["path"]).is_file()
    assert reconcile_wave(
        state,
        path,
        project=tmp_path,
        runtime={"checked": True, "local_idle": True, "remote_idle": True},
        compile_target=lambda p: {"ok": p.read_bytes() == original},
    )
    assert target.read_bytes() == original
    assert state["items"][0]["safe_to_continue"]
    assert not state["items"][0].get("new_attempts")


def test_awake_clock_counts_system_sleep(monkeypatch):
    """A budget clock must not stop while the host dozes.

    ``time.monotonic`` is CLOCK_UPTIME_RAW on macOS and freezes during sleep, so
    every timeout built on it silently became "N hours of awake time". Measured
    on the host that exposed this: one wave spanned 50,477s of wall clock while
    the monotonic clock advanced 4,246s, and ``watchdog_timeout`` was True on 0
    of 1548 recorded items across 127 runs.
    """
    import time

    from core.time import awake_clock

    # On this platform the sleep-inclusive clock must be reachable and distinct
    # from the sleep-frozen one, otherwise the fix is inert.

    if not hasattr(time, "CLOCK_MONOTONIC"):
        pytest.skip("platform has no CLOCK_MONOTONIC")
    inclusive = time.clock_gettime(time.CLOCK_MONOTONIC)
    frozen = time.monotonic()
    assert awake_clock() == pytest.approx(inclusive, abs=1.0)
    # The two differ by whatever the host has slept since boot; on a host that
    # has ever slept this is strictly positive, which is the whole point.
    assert inclusive >= frozen


def test_execute_defaults_to_the_sleep_inclusive_clock(scale):
    """Guard the binding: the wave's watchdog must use awake_clock."""
    assert scale.execute.__kwdefaults__["clock"].__name__ == "awake_clock"


def test_prune_exhausted_keys_drops_a_key_the_provider_calls_an_invalid_token(scale):
    """A retired credential must be pruned, not halt the run.

    The provider answers a dead key with "Invalid token". That wording matched
    none of the exhaustion patterns, so the batch was classified ``auth`` while
    no key was ever pruned and the run stopped with healthy keys still in the
    pool. Observed on the 2026-10-07 server test: two of four keys returned 401
    and only the remaining pair could serve work.
    """
    env = {"M2F_CODEX_API_KEYS": "one,two", "M2F_CODEX_API_KEY": "one"}
    diagnostic = (
        "Error code: 401 - {'error': {'code': '', 'message': 'Invalid token "
        "(request id: 202610071201028324013898268d9d6goC4tSSg)', "
        "'type': 'new_api_error'}}"
    )
    item = {
        "batch_id": "items-1.16",
        "classification": "auth",
        "credential_sha256": _fingerprint("one"),
        "new_attempts": [{"failure_class": "infrastructure", "reason": diagnostic}],
    }
    pruned, audits = scale.prune_exhausted_keys(env, [item])
    assert pruned["M2F_CODEX_API_KEYS"] == "two"
    assert pruned["M2F_CODEX_API_KEY"] == "two"
    assert [audit["fingerprint"] for audit in audits] == [_fingerprint("one")]


def test_prune_exhausted_keys_still_ignores_an_unnamed_transport_failure(scale):
    """Widening the patterns must not start retiring keys over ordinary errors."""
    env = {"M2F_CODEX_API_KEYS": "one,two"}
    item = {
        "batch_id": "items-2.6.5",
        "classification": "auth",
        "credential_sha256": _fingerprint("one"),
        "new_attempts": [{"final_diagnostic": "Connection error."}],
    }
    pruned, audits = scale.prune_exhausted_keys(env, [item])
    assert pruned is env
    assert audits == []


RELAY_UPSTREAM_400 = (
    "Error code: 400 - {'error': {'message': '服务可能有问题，请稍后重试或重新发起请求 "
    "(request id: x)', 'type': 'upstream_error', 'param': '', 'code': 'upstream_error'}}"
)
RELAY_CONCURRENCY_429 = (
    "Error code: 429 - {'error': {'message': 'Concurrency limit exceeded for user, please "
    "retry later', 'type': 'rate_limit_error', 'param': '', 'code': 'gateway_concurrency_limit'}}"
)


def test_relay_upstream_400_is_transient_not_infrastructure(scale):
    """The 2026-10-12 proof that gave up on its first call was classified this way."""
    attempt = {
        "stage": "proofs",
        "success": False,
        "failure_class": "infrastructure",
        "retry_class": "infrastructure",
        "reason": RELAY_UPSTREAM_400,
    }
    assert scale.failure_kind([attempt], 2) == "relay_transient"


def test_relay_concurrency_429_is_rate_limit_not_quota(scale):
    attempt = {"success": False, "final_diagnostic": RELAY_CONCURRENCY_429}
    assert scale.failure_kind([attempt], 1) == "rate_limit"


def test_real_auth_and_quota_failures_keep_their_kind(scale):
    assert (
        scale.failure_kind(
            [{"success": False, "final_diagnostic": "Error code: 401 - Invalid token"}], 1
        )
        == "auth"
    )
    assert scale.failure_kind([{"success": False, "final_diagnostic": "403 余额不足"}], 1) == "auth"
    assert (
        scale.failure_kind([{"success": False, "final_diagnostic": "insufficient balance"}], 1)
        == "quota"
    )


def test_relay_failures_pause_briefly_instead_of_ending_dispatch(scale):
    assert {"rate_limit", "relay_transient"} <= scale.SOFT_STOP_REASONS
    assert "quota" not in scale.SOFT_STOP_REASONS
    assert "auth" not in scale.SOFT_STOP_REASONS
    assert scale.RELAY_COOLDOWN_SECONDS < scale.FUSE_COOLDOWN_SECONDS


@pytest.mark.parametrize(
    "kind,diagnostic",
    [("relay_transient", RELAY_UPSTREAM_400), ("rate_limit", RELAY_CONCURRENCY_429)],
)
def test_a_relay_failure_refills_the_slot_instead_of_draining_the_wave(
    tmp_path, monkeypatch, scale, kind, diagnostic
):
    """One relay failure used to stop dispatch until the longest proof finished.

    On 2026-10-12 a 429 at 11:44 left two slots idle until 13:59, and a relay
    400 at 14:11 left three idle until the run was stopped. Every item here
    fails the same way, so the old behaviour dispatched only the first wave.
    """
    path = campaign(tmp_path, 8)
    options = SimpleNamespace(
        project=tmp_path,
        campaign=path,
        workers=2,
        max_items=4,
        max_wall=180,
        quota_limit=2_000_000,
        quote=tmp_path / "quote.json",
        no_infrastructure_fuse=False,
        no_infrastructure_fuse_source="test",
    )
    monkeypatch.setattr(scale, "quota_environment", lambda *args: {})
    monkeypatch.setattr(scale, "quota_status", lambda env: {"remaining_quota": 1_000_000})
    created = []

    class FakeProcess:
        def __init__(self, command, **kwargs):
            self.batch_id = command[command.index("--batch-id") + 1]
            self.pid = len(created) + 100
            self.log_path = Path(kwargs["stdout"].name)
            self.finished = False
            created.append(self)

        def poll(self):
            if not self.finished:
                data = json.loads(path.read_text())
                batch = next(b for b in data["batches"] if b["id"] == self.batch_id)
                attempt = {
                    "stage": "statements",
                    "success": False,
                    "worker_id": f"worker-{self.pid}",
                    "failure_class": "infrastructure",
                    "infrastructure_failure": True,
                    "final_diagnostic": diagnostic,
                }
                batch["attempts"].append(attempt)
                batch["last_outcome"] = attempt
                batch["status"] = "statement_retry"
                path.write_text(json.dumps(data))
                self.log_path.write_text(
                    json.dumps(
                        {"batch_id": self.batch_id, "stage": "statements", "outcome": attempt}
                    )
                    + "\n"
                )
                self.finished = True
            return 2

    # Advance far enough per tick that each relay cooldown expires.
    ticks = iter(range(0, 10_000_000, int(scale.RELAY_COOLDOWN_SECONDS) + 1))
    result = scale.execute(
        options, popen=FakeProcess, clock=lambda: next(ticks), pause=lambda _seconds: None
    )
    assert result["stop_reason"] == "item_limit"
    assert len(created) == 4, "every slot must be refilled after the cooldown"
    events = [
        json.loads(line)
        for line in (next((tmp_path / ".leanflow/scale-runs").iterdir()) / "events.jsonl")
        .read_text()
        .splitlines()
    ]
    paused = [e for e in events if e["event"] == "dispatch_paused"]
    assert paused and all(e["reason"] == kind for e in paused)
    assert all(e["resume_in_seconds"] == scale.RELAY_COOLDOWN_SECONDS for e in paused)
    assert not [e for e in events if e["event"] == "stop_dispatch" and e["reason"] == kind]
