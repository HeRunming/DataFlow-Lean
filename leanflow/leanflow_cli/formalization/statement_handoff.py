"""Integrate reviewed statements under a drained campaign's single-writer transaction."""

from __future__ import annotations

import hashlib
from collections.abc import Callable, Mapping
from datetime import UTC, datetime
from pathlib import Path
from typing import Any

from core.utils import atomic_json_write
from leanflow_cli.formalization.campaign_store import update_campaign_file
from leanflow_cli.formalization.corpus_campaign import lease_campaign_batches
from leanflow_cli.formalization.project_reachability import (
    _reachable_modules,
    project_target_reachability,
)
from leanflow_cli.formalization.statement_artifacts import (
    inspect_statement_artifact,
    reconcile_statement_artifacts,
)


def integrate_statement(
    batch: Mapping[str, Any],
    project: Path,
    compile_root: Callable[[Path], dict[str, Any]],
) -> dict[str, Any]:
    """Append one import, check the real root, and restore it on validation failure.

    Caller must own the controller lock with all workers drained. Never edit
    the target or treat root compilation with placeholders as a proved theorem.
    """
    artifact = inspect_statement_artifact(batch, project)
    result = {"batch_id": batch["id"], "success": False, **artifact}
    if not artifact["verified_source"]:
        return result
    reach = project_target_reachability(project, artifact["target_file"])
    if not reach["root_file"]:
        return {**result, "reason": "missing_project_root"}
    root = project / reach["root_file"]
    if root.is_symlink():
        return {**result, "reason": "invalid_project_root"}
    before = root.read_bytes()
    after = before
    if not reach["root_reachable"]:
        after = before.rstrip() + f"\nimport {reach['target_module']}\n".encode()
    transaction = (
        project
        / ".leanflow/handoff"
        / (
            hashlib.sha256(
                (str(batch["id"]) + artifact["source_sha256"]).encode()
            ).hexdigest()
            + ".json"
        )
    )
    atomic_json_write(
        transaction, {**result, "root_before": before.decode(), "state": "checking"}
    )
    root.write_bytes(after)
    _reachable_modules.cache_clear()
    try:
        check = compile_root(root)
        unchanged = (
            inspect_statement_artifact(batch, project).get("source_sha256")
            == artifact["source_sha256"]
        )
        success = (
            bool(check.get("success")) and unchanged and root.read_bytes() == after
        )
    except Exception as exc:
        check = {"success": False, "error": f"{type(exc).__name__}: {exc}"}
        success = False
    result.update(compile=check, root_file=reach["root_file"], success=success)
    if not success:
        if root.read_bytes() != after:
            raise RuntimeError(
                "project root changed during integration; refusing destructive rollback"
            )
        root.write_bytes(before)
        _reachable_modules.cache_clear()
        # Re-sync and compile the restored root on the authoritative host.
        result["rollback_compile"] = compile_root(root)
        result["reason"] = "integration_compile_failed"
        if not result["rollback_compile"].get("success"):
            atomic_json_write(
                transaction, {**result, "state": "rollback_needs_attention"}
            )
            raise RuntimeError("restored root could not be verified on the Lean host")
    else:
        result.update(
            reason="integrated",
            root_reachable=True,
            checked_at=datetime.now(UTC).isoformat(),
        )
    atomic_json_write(transaction, {**result, "state": "finished"})
    return result


def prepare_statement_handoff(
    campaign_path: Path,
    project: Path,
    *,
    compile_root: Callable[[Path], dict[str, Any]],
    excluded: set[str],
    limit: int = 4,
) -> dict[str, Any]:
    """Audit every artifact and integrate a bounded proof frontier before workers start."""

    def transform(current: Mapping[str, Any]) -> tuple[dict[str, Any], dict[str, Any]]:
        if any(b.get("lease") for b in current.get("batches", [])):
            raise RuntimeError("statement handoff requires a drained campaign")
        updated, audit = reconcile_statement_artifacts(current, project)
        integrations: list[dict[str, Any]] = []
        for batch in updated["batches"]:
            if len(integrations) >= limit:
                break
            if batch["id"] in excluded or not batch.get("statement_artifact", {}).get(
                "verified_source"
            ):
                continue
            reach = project_target_reachability(
                project, batch["statement_artifact"]["target_file"]
            )
            if reach["root_reachable"]:
                continue
            _, leased = lease_campaign_batches(
                updated,
                stage="proofs",
                worker_ids=["handoff-preview"],
                batch_id=batch["id"],
            )
            if not leased:
                continue
            result = integrate_statement(batch, project, compile_root)
            batch["statement_integration"] = result
            integrations.append(result)
        return updated, {"audit": audit, "integrations": integrations}

    return update_campaign_file(campaign_path, transform)
