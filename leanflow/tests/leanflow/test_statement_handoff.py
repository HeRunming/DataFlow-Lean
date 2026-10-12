"""Exercise artifact reconciliation and transactional statement-to-proof handoff."""

from __future__ import annotations

import hashlib
import json

import pytest

from leanflow_cli.formalization.corpus_campaign import (
    build_campaign,
    record_campaign_outcome,
)
from leanflow_cli.formalization.statement_artifacts import (
    inspect_statement_artifact,
    reconcile_statement_artifacts,
)
from leanflow_cli.formalization.statement_handoff import (
    integrate_statement,
    prepare_statement_handoff,
)


def fixture(tmp_path):
    source = "import Mathlib\ntheorem example_goal : True := by sorry\n"
    (tmp_path / "Item.lean").write_text(source)
    (tmp_path / "Main.lean").write_text("import Mathlib\n")
    review = {
        "batch_id": "item",
        "target_relative": "Item.lean",
        "lean_code": source,
        "candidate_digest": hashlib.sha256(source.encode()).hexdigest(),
    }
    (tmp_path / "review.json").write_text(json.dumps(review))
    attempt = {
        "stage": "statements",
        "success": True,
        "target_file": "Item.lean",
        "review_evidence": "review.json",
        "review_decision": "PASS",
        "provenance": "agent",
    }
    batch = {
        "id": "item",
        "labels": ["1"],
        "status": "statements_completed",
        "agent_status": "statements_completed",
        "attempts": [attempt],
        "last_outcome": attempt,
    }
    return batch


def rebuild(campaign):
    return build_campaign({"source_batches": campaign["batches"]}, existing=campaign)


def test_missing_target_never_resurrected_by_historical_success(tmp_path):
    batch = fixture(tmp_path)
    (tmp_path / "Item.lean").unlink()
    campaign, audit = reconcile_statement_artifacts({"batches": [batch]}, tmp_path)
    assert audit[0]["reason"] == "missing_target"
    assert campaign["batches"][0]["status"] == "statement_retry"
    rebuilt = rebuild(campaign)
    assert rebuilt["batches"][0]["agent_status"] == "statement_retry"
    assert rebuilt["batches"][0]["attempts"] == batch["attempts"]
    repaired = record_campaign_outcome(rebuilt, batch_id="item", outcome=batch["attempts"][0])
    assert repaired["batches"][0]["agent_status"] == "statements_completed"
    assert "stale_statement_receipt" not in repaired["batches"][0]


def test_changed_proof_is_preserved_for_review(tmp_path):
    batch = fixture(tmp_path)
    path = tmp_path / "Item.lean"
    path.write_text(path.read_text().replace("sorry", "trivial"))
    before = path.read_bytes()
    campaign, _ = reconcile_statement_artifacts({"batches": [batch]}, tmp_path)
    assert campaign["batches"][0]["status"] == "artifact_review_required"
    assert path.read_bytes() == before


def proof_review_fixture(tmp_path, batch):
    path = tmp_path / "Item.lean"
    accepted = hashlib.sha256(path.read_bytes()).hexdigest()
    path.write_text(
        path.read_text().replace(
            "theorem example_goal",
            "private theorem helper : True := by trivial\ntheorem example_goal",
        )
    )
    digest = hashlib.sha256(path.read_bytes()).hexdigest()
    receipt = {
        "schema": "leanflow.operator_proof_source_review.v1",
        "reviewer": "operator",
        "review_decision": "PASS",
        "statement_fidelity_findings": "Only a checked private helper was inserted; original source is unchanged.",
        "batch_id": batch["id"],
        "target_relative": "Item.lean",
        "accepted_sha256": accepted,
        "source_sha256": digest,
        "lean_code": path.read_text(),
        "remote_compile_receipt": {
            "schema": "leanflow.remote_compile_receipt.v1",
            "exit_code": 0,
            "target_sha256": digest,
        },
    }
    review_path = tmp_path / ".leanflow/proof-source-reviews" / f"item-{digest}.json"
    review_path.parent.mkdir(parents=True)
    review_path.write_text(json.dumps(receipt))
    return review_path, receipt


def test_operator_review_admits_checked_helper_without_completing_parent(tmp_path):
    batch = fixture(tmp_path)
    proof_review_fixture(tmp_path, batch)
    campaign, audit = reconcile_statement_artifacts({"batches": [batch]}, tmp_path)
    assert audit[0]["reason"] == "reviewed_proof_progress"
    assert campaign["batches"][0]["status"] == "statements_completed"
    assert "sorry" in (tmp_path / "Item.lean").read_text()
    assert campaign["batches"][0]["attempts"] == batch["attempts"]


@pytest.mark.parametrize(
    "mutation", ["batch", "accepted", "compile", "compile_hash", "code", "source", "decision"]
)
def test_recovery_review_rejects_unbound_or_changed_evidence(tmp_path, mutation):
    batch = fixture(tmp_path)
    path, receipt = proof_review_fixture(tmp_path, batch)
    if mutation == "batch":
        receipt["batch_id"] = "other"
    elif mutation == "accepted":
        receipt["accepted_sha256"] = "wrong"
    elif mutation == "compile":
        receipt["remote_compile_receipt"]["exit_code"] = 1
    elif mutation == "compile_hash":
        receipt["remote_compile_receipt"]["target_sha256"] = "wrong"
    elif mutation == "code":
        receipt["lean_code"] += "\n"
    elif mutation == "decision":
        receipt["review_decision"] = "BLOCK"
    else:
        target = tmp_path / "Item.lean"
        target.write_text(target.read_text().replace("example_goal : True", "example_goal : False"))
    path.write_text(json.dumps(receipt))
    assert inspect_statement_artifact(batch, tmp_path)["reason"] == "source_changed_since_review"


def test_import_shell_and_wrong_evidence_do_not_pass(tmp_path):
    batch = fixture(tmp_path)
    (tmp_path / "Item.lean").write_text("import Mathlib\n-- theorem fake : True := by sorry\n")
    assert inspect_statement_artifact(batch, tmp_path)["reason"] == "empty_import_shell"
    fixture(tmp_path)
    review = json.loads((tmp_path / "review.json").read_text())
    review["batch_id"] = "other"
    (tmp_path / "review.json").write_text(json.dumps(review))
    assert not inspect_statement_artifact(batch, tmp_path)["verified_source"]


def test_success_imports_exact_target_without_promoting_proof(tmp_path):
    batch = fixture(tmp_path)
    checks = []

    def compile_root(path):
        checks.append(path.read_text())
        return {"success": True}

    result = integrate_statement(batch, tmp_path, compile_root)
    assert result["success"]
    assert "import Item" in checks[0]
    assert batch["status"] == "statements_completed"
    assert "sorry" in (tmp_path / "Item.lean").read_text()


def test_failed_root_build_restores_then_rechecks_root(tmp_path):
    batch = fixture(tmp_path)
    before = (tmp_path / "Main.lean").read_bytes()
    checks = []

    def compile_root(path):
        checks.append(path.read_bytes())
        return {"success": len(checks) == 2}

    result = integrate_statement(batch, tmp_path, compile_root)
    assert not result["success"]
    assert checks[1] == before == (tmp_path / "Main.lean").read_bytes()


def test_handoff_respects_dependencies_and_exclusions(tmp_path):
    batch = fixture(tmp_path)
    batch["dependency_labels"] = ["missing"]
    path = tmp_path / "campaign.json"
    path.write_text(json.dumps({"batches": [batch]}))

    def no_compile(_):
        raise AssertionError("must not compile an ineligible target")

    result = prepare_statement_handoff(path, tmp_path, compile_root=no_compile, excluded=set())
    assert not result["integrations"]
    batch["dependency_labels"] = []
    path.write_text(json.dumps({"batches": [batch]}))
    result = prepare_statement_handoff(path, tmp_path, compile_root=no_compile, excluded={"item"})
    assert not result["integrations"]
