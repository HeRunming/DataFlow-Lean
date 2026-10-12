"""Checkpoint the durable plan together with proof sources for campaign recovery."""

from __future__ import annotations

import base64
import re
from pathlib import Path
from typing import Any

from core.utils import atomic_json_write

ARTIFACTS = ("blueprint.json", "summary.json", "plan.md", "journal.jsonl", "current.json")


def plan_directory(project: Path, batch_id: str) -> Path:
    """Resolve exactly one batch plan without permitting path traversal or symlinks."""
    if not re.fullmatch(r"[A-Za-z0-9_.-]+", batch_id) or batch_id in {".", ".."}:
        raise ValueError("invalid recovery batch id")
    directory = project.resolve() / ".leanflow" / "campaign-plan-state" / batch_id
    if directory.resolve() != directory:
        raise ValueError("recovery plan directory contains a symlink")
    return directory


def capture_plan(project: Path, batch_id: str) -> dict[str, Any]:
    """Capture only named plan artifacts; process logs and locks remain untouched."""
    directory = plan_directory(project, batch_id)
    files = {}
    for name in ARTIFACTS:
        path = directory / name
        if path.is_symlink():
            raise ValueError("recovery plan artifact is a symlink")
        if path.exists():
            files[name] = base64.b64encode(path.read_bytes()).decode()
    return {"batch_id": batch_id, "files": files}


def validate_plan(snapshot: dict[str, Any], batch_id: str) -> dict[str, bytes]:
    """Validate every snapshot member before recovery changes any source."""
    if snapshot.get("batch_id") != batch_id or not isinstance(snapshot.get("files"), dict):
        raise ValueError("proof plan snapshot scope mismatch")
    if set(snapshot["files"]) - set(ARTIFACTS):
        raise ValueError("invalid proof plan snapshot path")
    return {name: base64.b64decode(data, validate=True) for name, data in snapshot["files"].items()}


def restore_plan(
    project: Path, batch_id: str, expected: dict[str, bytes], *, archive: Path
) -> dict[str, Any]:
    """Restore source-coherent plan bytes after archiving all failed-attempt state.

    Legacy source-only snapshots reset active plan artifacts, keeping the old
    state in the archive. Startup rebuilds the graph from restored sources;
    it must not retain proved nodes or consumed-helper markers from lost edits.
    """
    current = capture_plan(project, batch_id)
    if not archive.exists():
        atomic_json_write(archive, current)
    directory = plan_directory(project, batch_id)
    directory.mkdir(parents=True, exist_ok=True)
    for name, content in expected.items():
        path = directory / name
        temporary = path.with_suffix(path.suffix + ".recovery-tmp")
        temporary.write_bytes(content)
        temporary.replace(path)
    for name in set(current["files"]) - set(expected):
        (directory / name).unlink()
    actual = validate_plan(capture_plan(project, batch_id), batch_id)
    if actual != expected:
        raise RuntimeError("restored plan differs from its snapshot")
    return {"restored": True, "archive": str(archive), "files": sorted(expected)}
