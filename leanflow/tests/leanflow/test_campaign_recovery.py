"""Exercise lossless failed-proof recovery and precise process recognition."""

import base64
import json
from pathlib import Path

import pytest

from leanflow_cli.formalization import campaign_recovery as recovery


def test_process_probe_ignores_shell_and_grep_descriptions():
    text = """
101 /bin/zsh -lc "ps | rg 'leanflow/remote-bin/lake -m leanflow_cli.main'"
102 rg -m leanflow_cli.main
103 /usr/local/bin/python -m leanflow_cli.native.native_runner
104 /usr/local/bin/python3.12 -m agent.providers.isolated_auxiliary
105 /bin/bash /Users/test/leanflow/remote-bin/lake env lean Main.lean
106 /usr/local/bin/python unrelated.py
107 /usr/local/bin/python -u /tmp/lean-probe-service.py
"""
    assert recovery.local_runtime_pids(text) == [103, 104, 105, 107]


def case(tmp_path):
    target = tmp_path / "Book" / "Batch" / "Main.lean"
    target.parent.mkdir(parents=True)
    target.write_text("theorem original : True := by sorry\n")
    item = {
        "batch_id": "b",
        "stage": "proofs",
        "target_path": str(target),
        "worker_id": "w",
        "attempts_before": 0,
        "classification": "infrastructure",
        "proof_snapshot": recovery.capture_proof_snapshot(
            target, tmp_path, tmp_path / ".leanflow/before.json"
        ),
    }
    return target, item, {"id": "b", "status": "statements_completed", "attempts": []}


def test_restore_archives_edits_and_helpers_then_retries_idempotently(tmp_path):
    target, item, batch = case(tmp_path)
    original = target.read_bytes()
    candidate = "theorem changed : False := by sorry\n"
    target.write_text(candidate)
    target.with_name("Helper.lean").write_text("axiom bad : False\n")
    result = recovery.restore_failed_proof(item, batch, project=tmp_path)
    assert target.read_bytes() == original
    assert not target.with_name("Helper.lean").exists()
    archived = Path(result["archive"]).read_bytes()
    assert base64.b64decode(json.loads(archived)["files"]["Main.lean"]).decode() == candidate
    recovery.restore_failed_proof(item, batch, project=tmp_path)
    assert Path(result["archive"]).read_bytes() == archived
    assert batch["status"] == "statements_completed"
    assert batch["attempts"] == []


def test_failed_worker_restores_matching_graph_and_helper_delivery_state(tmp_path):
    target, item, batch = case(tmp_path)
    plan = tmp_path / ".leanflow/campaign-plan-state/b"
    plan.mkdir(parents=True)
    initial = {
        "blueprint.json": '{"nodes":[{"name":"original","status":"stated"}]}',
        "summary.json": '{"pending_research_helper_candidate":{"state":"ready_to_integrate"}}',
        "journal.jsonl": '{"event":"checked-helper"}\n',
    }
    for name, data in initial.items():
        (plan / name).write_text(data)
    item["proof_snapshot"] = recovery.capture_proof_snapshot(
        target, tmp_path, tmp_path / ".leanflow/paired.json", batch_id="b"
    )
    target.write_text("theorem helper : True := by trivial\ntheorem original : True := by sorry\n")
    (plan / "blueprint.json").write_text('{"nodes":[{"name":"helper","status":"proved"}]}')
    (plan / "summary.json").write_text('{"resolved_research_helper_candidates":["helper"]}')
    (plan / "plan.md").write_text("new helper proved")
    result = recovery.restore_failed_proof(item, batch, project=tmp_path)
    assert "helper" not in target.read_text()
    assert not result["plan"]["legacy_reset"]
    for name, data in initial.items():
        assert (plan / name).read_text() == data
    assert not (plan / "plan.md").exists()
    archive = Path(result["plan"]["archive"])
    saved = archive.read_bytes()
    assert "helper" in base64.b64decode(json.loads(saved)["files"]["blueprint.json"]).decode()
    recovery.restore_failed_proof(item, batch, project=tmp_path)
    assert archive.read_bytes() == saved


def test_legacy_restore_archives_stale_plan_and_rebuilds_from_source(tmp_path):
    target, item, batch = case(tmp_path)
    plan = tmp_path / ".leanflow/campaign-plan-state/b"
    plan.mkdir(parents=True)
    (plan / "blueprint.json").write_text('{"nodes":[{"name":"lost","status":"proved"}]}')
    (plan / "summary.json").write_text('{"resolved_research_helper_candidates":["lost"]}')
    (plan / "blueprint.lock").write_text("lock retained")
    result = recovery.restore_failed_proof(item, batch, project=tmp_path)
    assert result["plan"]["legacy_reset"]
    assert not (plan / "blueprint.json").exists()
    assert not (plan / "summary.json").exists()
    assert (plan / "blueprint.lock").read_text() == "lock retained"


def test_plan_symlink_blocks_source_rollback(tmp_path):
    target, item, batch = case(tmp_path)
    plan = tmp_path / ".leanflow/campaign-plan-state/b"
    plan.mkdir(parents=True)
    (plan / "summary.json").symlink_to(target)
    target.write_text("new source must remain until recovery is safe")
    with pytest.raises(ValueError, match="symlink"):
        recovery.restore_failed_proof(item, batch, project=tmp_path)
    assert target.read_text() == "new source must remain until recovery is safe"


def test_interrupted_plan_restore_cannot_mark_wave_safe(tmp_path, monkeypatch):
    target, item, batch = case(tmp_path)
    target.write_text("invalid candidate")
    campaign = tmp_path / "campaign.json"
    campaign.write_text(json.dumps({"batches": [batch]}))
    state = {"active": {}, "items": [item]}
    idle = {"checked": True, "local_idle": True, "remote_idle": True}
    original = recovery.restore_plan

    def fail(*args, **kwargs):
        raise OSError("interrupted plan restore")

    monkeypatch.setattr(recovery, "restore_plan", fail)
    assert not recovery.reconcile_wave(
        state, campaign, project=tmp_path, runtime=idle, compile_target=lambda p: {"ok": True}
    )
    assert not item.get("safe_to_continue")
    monkeypatch.setattr(recovery, "restore_plan", original)
    assert recovery.reconcile_wave(
        state, campaign, project=tmp_path, runtime=idle, compile_target=lambda p: {"ok": True}
    )
    assert item["safe_to_continue"]


def test_verified_helper_in_baseline_survives_later_failed_attempt(tmp_path):
    target, item, batch = case(tmp_path)
    source = "theorem helper : True := by trivial\ntheorem original : True := by sorry\n"
    target.write_text(source)
    plan = tmp_path / ".leanflow/campaign-plan-state/b"
    plan.mkdir(parents=True)
    graph = '{"nodes":[{"name":"helper","status":"proved"}]}'
    (plan / "blueprint.json").write_text(graph)
    item["proof_snapshot"] = recovery.capture_proof_snapshot(
        target, tmp_path, tmp_path / ".leanflow/with-helper.json", batch_id="b"
    )
    target.write_text(source.replace("by sorry", "by nonexistent_tactic"))
    recovery.restore_failed_proof(item, batch, project=tmp_path)
    assert target.read_text() == source
    assert (plan / "blueprint.json").read_text() == graph


@pytest.mark.parametrize("violation", ["digest", "lease", "success", "other_worker", "symlink"])
def test_restore_refuses_changed_authority(tmp_path, violation):
    target, item, batch = case(tmp_path)
    if violation == "digest":
        item["proof_snapshot"]["sha256"] = "bad"
    elif violation == "lease":
        batch["lease"] = {"worker_id": "w"}
    elif violation == "success":
        batch["attempts"] = [{"worker_id": "w", "success": True}]
    elif violation == "other_worker":
        batch["attempts"] = [{"worker_id": "other", "success": False}]
    else:
        target.with_name("external.lean").symlink_to(target)
    before = target.read_bytes()
    with pytest.raises(ValueError):
        recovery.restore_failed_proof(item, batch, project=tmp_path)
    assert target.read_bytes() == before


def test_reconciliation_waits_for_writers_and_compile_then_defers(tmp_path):
    target, item, batch = case(tmp_path)
    target.write_text("unverified candidate")
    campaign = tmp_path / "campaign.json"
    campaign.write_text(json.dumps({"batches": [batch]}))
    state = {"active": {}, "items": [item]}
    idle = {"checked": True, "local_idle": True, "remote_idle": True}
    check = lambda p: {"ok": False, "exit_code": 124}
    assert not recovery.reconcile_wave(
        state,
        campaign,
        project=tmp_path,
        runtime={**idle, "local_idle": False},
        compile_target=check,
    )
    assert target.read_text() == "unverified candidate"
    assert not recovery.reconcile_wave(
        state, campaign, project=tmp_path, runtime=idle, compile_target=check
    )
    assert not item.get("safe_to_continue")
    assert recovery.reconcile_wave(
        state,
        campaign,
        project=tmp_path,
        runtime=idle,
        compile_target=lambda p: {"ok": True},
    )
    assert item["safe_to_continue"]
    assert not item["receipt_recovery"]["safe_to_retry"]
    assert json.loads(campaign.read_text())["batches"][0]["status"] == "statements_completed"


def test_quarantine_excludes_transitive_consumers(tmp_path):
    campaign = tmp_path / "campaign.json"
    campaign.write_text(
        json.dumps(
            {
                "batches": [
                    {"id": "a", "labels": ["A"]},
                    {"id": "b", "labels": ["B"], "dependency_labels": ["A"]},
                    {"id": "c", "labels": ["C"], "soft_dependency_labels": ["B"]},
                    {"id": "d", "labels": ["D"]},
                ]
            }
        )
    )
    assert recovery.dependent_exclusions(campaign, {"a"}) == {"a", "b", "c"}


@pytest.mark.parametrize("owner, ready", [("w", True), ("other", False)])
def test_idle_recovery_releases_only_exited_workers_own_lease(tmp_path, owner, ready):
    target, item, batch = case(tmp_path)
    item["exit_code"] = 1
    batch["lease"] = {"worker_id": owner, "stage": "proofs"}
    campaign = tmp_path / "campaign.json"
    campaign.write_text(json.dumps({"batches": [batch]}))
    state = {"items": [item], "active": {}}
    assert (
        recovery.reconcile_wave(
            state,
            campaign,
            project=tmp_path,
            runtime={"checked": True, "local_idle": True, "remote_idle": True},
            compile_target=lambda p: {"ok": True},
        )
        is ready
    )
    saved = json.loads(campaign.read_text())["batches"][0]
    assert bool(saved.get("lease")) is not ready
    assert saved["attempts"] == []


def test_own_warm_probe_pids_recognizes_the_service_behind_its_wrapper():
    """Match the probe however the single-host launch spelled its argv.

    On a single host the orchestrator runs its own warm probe before dispatch, so
    the service argv appears in the process table in the normal course of a run.
    """
    text = """
100 /bin/bash -lc service_dir=/srv/lean/.leanflow-remote-warm-probe.AB; trap x EXIT; cd /p && /usr/bin/timeout --signal=TERM --kill-after=1s 3600s python3 -u /srv/lean/.leanflow-remote-warm-probe.AB/lean-probe-service.py
101 /usr/bin/timeout --signal=TERM --kill-after=1s 3600s python3 -u /srv/lean/.leanflow-remote-warm-probe.AB/lean-probe-service.py
102 python3 -m leanflow_cli.formalization.corpus_campaign_runner /c.json
103 /srv/lean/leanflow/remote-bin/lake env lean /x.lean
"""
    assert recovery.own_warm_probe_pids(text) == [100, 101]


def test_idle_check_does_not_count_the_runs_own_warm_probe_as_busy(monkeypatch):
    """The run's own probe must not make every restart refuse itself.

    Reproduces the single-host failure: the probe is alive, so ``local_runtime_pids``
    reported a busy runtime, ``execute`` raised "statement handoff requires idle
    local and remote runtimes", and the run died seconds after starting -- while
    the probe it was tripping over was its own.
    """
    text = """
101 /usr/local/bin/python -u /srv/lean/.leanflow-remote-warm-probe.AB/lean-probe-service.py
"""
    monkeypatch.setenv("HDP_LOCAL_LEAN_HOST", "1")
    busy = recovery.local_runtime_pids(text)
    own = recovery.own_warm_probe_pids(text)
    assert busy == [101], "the probe is still recognized as a runtime"
    assert own == [101], "and is attributed to the probe, not to real work"
    assert [pid for pid in busy if pid not in own] == [], "so it is not busy on its own"
