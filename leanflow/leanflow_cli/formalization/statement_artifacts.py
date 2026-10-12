"""Audit current statement artifacts without turning historical receipts into readiness."""

from __future__ import annotations

import hashlib
import json
import re
from collections.abc import Mapping
from pathlib import Path
from typing import Any

from leanflow_cli.formalization.proof_source_review import reviewed_proof_source
from leanflow_cli.lean.lean_parsing import _strip_lean_comments_and_strings

_DECLARATION = re.compile(
    r"(?m)^\s*(?:(?:noncomputable|private|protected|unsafe)\s+)*"
    r"(?:theorem|lemma|example|def|abbrev|structure|class|inductive)\b"
)


def latest_statement(batch: Mapping[str, Any]) -> dict[str, Any]:
    """Return the latest successful statement receipt, preserving failed proof outcomes."""
    return next(
        (
            dict(a)
            for a in reversed(batch.get("attempts", []))
            if isinstance(a, Mapping) and a.get("stage") == "statements" and a.get("success")
        ),
        {},
    )


def inspect_statement_artifact(batch: Mapping[str, Any], project: Path) -> dict[str, Any]:
    """Check the target and bind automated integration to an exact accepted review source."""
    accepted = latest_statement(batch)
    relative = str(accepted.get("target_file", "") or "")
    result: dict[str, Any] = {
        "target_file": relative,
        "reason": "no_accepted_statement" if not accepted else "missing_target_receipt",
        "verified_source": False,
    }
    if not relative:
        return result
    root = project.resolve()
    target = root / relative
    if target.resolve() != target or not target.is_relative_to(root) or target.suffix != ".lean":
        return {**result, "reason": "invalid_target_path"}
    if not target.is_file():
        return {**result, "reason": "missing_target"}
    try:
        raw = target.read_bytes()
        text = raw.decode("utf-8")
    except (OSError, UnicodeError):
        return {**result, "reason": "unreadable_target"}
    result["source_sha256"] = hashlib.sha256(raw).hexdigest()
    if not _DECLARATION.search(_strip_lean_comments_and_strings(text)):
        return {**result, "reason": "empty_import_shell"}
    evidence = root / str(accepted.get("review_evidence", "") or "")
    if (
        evidence.resolve() != evidence
        or not evidence.is_relative_to(root)
        or evidence.suffix != ".json"
        or not evidence.is_file()
    ):
        return {**result, "reason": "legacy_review_unverified"}
    try:
        review = json.loads(evidence.read_text())
        code = str(review.get("lean_code", ""))
        expected = hashlib.sha256(code.encode()).hexdigest()
        valid = (
            review.get("batch_id") == batch.get("id")
            and review.get("target_relative") == relative
            and review.get("candidate_digest") == expected
            and str(accepted.get("review_decision", "")).upper() == "PASS"
        )
    except (OSError, ValueError, AttributeError):
        valid = False
        expected = ""
    result["review_evidence"] = str(evidence.relative_to(root))
    result["accepted_sha256"] = expected
    if not valid:
        return {**result, "reason": "invalid_review_evidence"}
    if result["source_sha256"] != expected:
        if reviewed_proof_source(
            root, str(batch.get("id", "")), relative, expected, result["source_sha256"]
        ):
            return {**result, "reason": "reviewed_proof_progress", "verified_source": True}
        return {**result, "reason": "source_changed_since_review"}
    return {**result, "reason": "verified_source", "verified_source": True}


def reconcile_statement_artifacts(
    campaign: Mapping[str, Any], project: Path
) -> tuple[dict[str, Any], list[dict[str, Any]]]:
    """Downgrade missing artifacts and quarantine changed sources, preserving all attempts.

    Completed proofs have their separate proof reconciliation. Legacy reviews
    stay visible but cannot be newly integrated without fresh evidence.
    """
    updated = {**campaign, "batches": [dict(b) for b in campaign.get("batches", [])]}
    audit = []
    repairable = {"missing_target", "empty_import_shell", "missing_target_receipt"}
    quarantined = {
        "source_changed_since_review",
        "invalid_review_evidence",
        "invalid_target_path",
    }
    for batch in updated["batches"]:
        if batch.get("lease") or batch.get("status") in {
            "completed",
            "proofs_completed",
        }:
            continue
        if not latest_statement(batch):
            continue
        artifact = inspect_statement_artifact(batch, project)
        batch["statement_artifact"] = artifact
        audit.append({"batch_id": batch["id"], **artifact})
        reason = artifact["reason"]
        if reason not in repairable | quarantined:
            continue
        next_status = "statement_retry" if reason in repairable else "artifact_review_required"
        # Do not move the boundary on repeated audits while repair is pending.
        batch.setdefault(
            "stale_statement_receipt",
            {
                "reason": reason,
                "attempt_count": len(batch.get("attempts", [])),
                "next_status": next_status,
                "target_file": artifact["target_file"],
            },
        )
        batch["status"] = batch["agent_status"] = next_status
    return updated, audit
