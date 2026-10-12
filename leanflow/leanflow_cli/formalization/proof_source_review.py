"""Validate explicit operator reviews of recovered proof progress for admission."""

from __future__ import annotations

import hashlib
import json
import re
from pathlib import Path


def reviewed_proof_source(
    project: Path, batch_id: str, target: str, accepted_sha256: str, source_sha256: str
) -> bool:
    """Bind an operator-reviewed recovery to both sources and a remote compile.

    These receipts are written by the recovery operator after checking statement
    fidelity, never automatically from a proved DAG node or compilation alone.
    They authorize resuming proof work, not marking the parent theorem proved.
    """
    if not re.fullmatch(r"[A-Za-z0-9_.-]+", batch_id):
        return False
    root = project.resolve()
    path = root / ".leanflow/proof-source-reviews" / f"{batch_id}-{source_sha256}.json"
    if path.resolve() != path or not path.is_file():
        return False
    try:
        receipt = json.loads(path.read_text())
        compile_receipt = receipt.get("remote_compile_receipt", {})
        return bool(
            receipt.get("schema") == "leanflow.operator_proof_source_review.v1"
            and receipt.get("reviewer") == "operator"
            and receipt.get("review_decision") == "PASS"
            and receipt.get("statement_fidelity_findings")
            and receipt.get("batch_id") == batch_id
            and receipt.get("target_relative") == target
            and receipt.get("accepted_sha256") == accepted_sha256
            and receipt.get("source_sha256") == source_sha256
            and hashlib.sha256(receipt["lean_code"].encode()).hexdigest() == source_sha256
            and compile_receipt.get("schema") == "leanflow.remote_compile_receipt.v1"
            and compile_receipt.get("exit_code") == 0
            and compile_receipt.get("target_sha256") == source_sha256
        )
    except (OSError, ValueError, TypeError, KeyError, AttributeError):
        return False
