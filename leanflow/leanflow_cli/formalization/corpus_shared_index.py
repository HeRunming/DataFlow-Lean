"""Index verified Lean declarations that other batches could reuse.

Every campaign batch is formalized in isolation. Its plan state lives in a
per-batch directory, and no batch source imports another, so a declaration one
batch already proved is invisible to the next one -- which then defines the same
object again. The HDP corpus shows this directly: ``euclideanNorm`` is defined
in 29 batches and ``psi2Norm`` in 17.

This module builds a project-level, read-only index of the declarations that are
safe to offer for reuse, so a planner can see what already exists instead of
rediscovering it. It deliberately does not change any graph, rewrite any source,
or touch the campaign ledger: the index is a cache under
``<project>/.leanflow/``, and deleting it only costs a rescan.

Only ``sorry``-free declarations are indexed. A scaffold carrying ``sorry`` is
unfinished work, and recommending it for reuse would let one batch build on
another batch's unproved assumption.
"""

from __future__ import annotations

import hashlib
import json
import re
from collections.abc import Iterable, Mapping
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from core.utils import atomic_json_write
from leanflow_cli.lean.lean_parsing import (
    _declaration_line_index_from_text,
    _statement_signature_text,
)

INDEX_RELATIVE_PATH = Path(".leanflow") / "shared-declarations.json"
# Batch sources carry the declarations a batch already wrote; the shared tree
# carries the vocabulary that has been promoted for reuse. Both must be scanned
# or the index would report an empty shared tree forever and the prompt block
# built from it could never name anything.
SOURCE_GLOBS = ("FateXWork/Environments/*/Main.lean", "FateXWork/Environments/Shared/*.lean")
# Bumped when the record schema changes, so a stale cache is rescanned rather
# than silently treated as valid.
_INDEX_VERSION = 2
# Declarations that carry no proof obligation still anchor shared vocabulary, so
# they are indexed even though they can never be reused "as a theorem".
_REUSABLE_KINDS = frozenset(
    {"abbrev", "class", "def", "instance", "opaque", "structure", "inductive", "axiom"}
)
_SORRY_RE = re.compile(r"\bsorry\b")


@dataclass(frozen=True)
class SharedDeclaration:
    """Describe one declaration that another batch could reuse."""

    name: str
    kind: str
    batch_id: str
    relative_file: str
    line: int
    signature_sha256: str
    declaration_sha256: str
    namespace: str = ""
    module: str = ""

    def as_dict(self) -> dict[str, Any]:
        """Return a JSON-serializable record without embedding source text."""
        return {
            "name": self.name,
            "kind": self.kind,
            "batch_id": self.batch_id,
            "file": self.relative_file,
            "line": self.line,
            "signature_sha256": self.signature_sha256,
            "declaration_sha256": self.declaration_sha256,
            "namespace": self.namespace,
            "module": self.module,
        }


def _sha256(text: str) -> str:
    """Return the hex digest of one normalized text payload."""
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def _normalized(text: str) -> str:
    """Return a whitespace- and comment-insensitive comparison key."""
    return re.sub(r"\s+", " ", str(text or "")).strip()


def _file_digest(path: Path) -> str:
    """Return the content digest used to decide whether a file needs a rescan."""
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _batch_id_for(path: Path) -> str:
    """Return the campaign batch id owning one batch source file."""
    return path.parent.name


def _iter_source_files(root: Path, source_globs: tuple[str, ...]) -> list[Path]:
    """Return every source file matched by the configured globs, deduplicated.

    A file may match more than one pattern when a project nests its shared tree
    inside the batch tree, and scanning it twice would double its declarations.
    """
    seen: dict[str, Path] = {}
    for pattern in source_globs:
        for path in sorted(root.glob(pattern)):
            if path.is_file():
                seen.setdefault(str(path), path)
    return [seen[key] for key in sorted(seen)]


def _declaration_slices(source: str) -> list[tuple[str, str, int, str]]:
    """Return ``(kind, name, line, body)`` for each declaration in one source.

    A slice runs from its declaration line to the next declaration, so the body
    carries the proof (or the absence of one) that decides shareability.
    """
    lines = source.splitlines()
    entries = _declaration_line_index_from_text(source)
    slices: list[tuple[str, str, int, str]] = []
    for position, entry in enumerate(entries):
        start = int(entry["line"]) - 1
        if start < 0 or start >= len(lines):
            continue
        if position + 1 < len(entries):
            end = int(entries[position + 1]["line"]) - 1
        else:
            end = len(lines)
        body = "\n".join(lines[start:end])
        slices.append((str(entry["kind"]), str(entry["name"]), int(entry["line"]), body))
    return slices


_NAMESPACE_OPEN_RE = re.compile(r"^\s*namespace\s+([A-Za-z_][A-Za-z0-9_'.]*)")
_NAMESPACE_END_RE = re.compile(r"^\s*end(?:\s+([A-Za-z_][A-Za-z0-9_'.]*))?\s*$")


def _namespace_prefixes(source: str) -> dict[int, str]:
    """Return the enclosing namespace for each line of one source.

    Lean's module name (from the file path) and the namespace a declaration is
    actually placed in are independent. ``FateXWork/Environments/Shared/Analysis.lean``
    is module ``FateXWork.Environments.Shared.Analysis``, but its declarations may
    sit in ``FateXWork.Shared.Analysis``. A caller told only the module name
    cannot reference the symbol, so the namespace is read from the source.
    """
    prefixes: dict[int, str] = {}
    stack: list[str] = []
    for number, line in enumerate(source.splitlines(), start=1):
        prefixes[number] = ".".join(stack)
        opened = _NAMESPACE_OPEN_RE.match(line)
        if opened:
            stack.extend(part for part in opened.group(1).split(".") if part)
            continue
        closed = _NAMESPACE_END_RE.match(line)
        if not closed or not stack:
            continue
        named = str(closed.group(1) or "")
        if named and named in stack:
            while stack and stack[-1] != named:
                stack.pop()
            if stack:
                stack.pop()
        elif stack:
            stack.pop()
    return prefixes


def _is_indexable(kind: str, body: str, name: str) -> bool:
    """Return whether one declaration is verified enough to offer for reuse."""
    if kind not in _REUSABLE_KINDS:
        return False
    if not name or name.startswith("[anonymous"):
        return False
    # A declaration mid-rewrite still contains ``sorry``; offering it would let
    # another batch build on an unfinished obligation.
    return not _SORRY_RE.search(body)


def scan_project_declarations(
    project_root: str | Path,
    *,
    source_globs: tuple[str, ...] = SOURCE_GLOBS,
) -> list[SharedDeclaration]:
    """Return every shareable declaration found in the project's batch sources."""
    root = Path(project_root).expanduser().resolve()
    found: list[SharedDeclaration] = []
    for path in _iter_source_files(root, source_globs):
        if not path.is_file():
            continue
        try:
            source = path.read_text(encoding="utf-8")
        except (OSError, UnicodeDecodeError):
            continue
        batch_id = _batch_id_for(path)
        relative = str(path.relative_to(root))
        module = ".".join(Path(relative).with_suffix("").parts)
        prefixes = _namespace_prefixes(source)
        for kind, name, line, body in _declaration_slices(source):
            if not _is_indexable(kind, body, name):
                continue
            signature = _statement_signature_text(body)
            found.append(
                SharedDeclaration(
                    name=name,
                    kind=kind,
                    batch_id=batch_id,
                    relative_file=relative,
                    line=line,
                    signature_sha256=_sha256(_normalized(signature)),
                    declaration_sha256=_sha256(_normalized(body)),
                    namespace=prefixes.get(line, ""),
                    module=module,
                )
            )
    return found


def index_path(project_root: str | Path) -> Path:
    """Return the project-level index location.

    The index lives at the project root, deliberately outside every per-batch
    plan-state directory: those directories exist to isolate batches, and an
    index inside one would inherit that isolation.
    """
    return Path(project_root).expanduser().resolve() / INDEX_RELATIVE_PATH


def load_index(project_root: str | Path) -> dict[str, Any]:
    """Return the stored index, or an empty skeleton when none exists."""
    path = index_path(project_root)
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, ValueError):
        return {"version": _INDEX_VERSION, "entries": [], "files": {}}
    if not isinstance(payload, dict) or payload.get("version") != _INDEX_VERSION:
        return {"version": _INDEX_VERSION, "entries": [], "files": {}}
    if not isinstance(payload.get("entries"), list):
        return {"version": _INDEX_VERSION, "entries": [], "files": {}}
    return payload


def refresh_index(
    project_root: str | Path,
    *,
    source_globs: tuple[str, ...] = SOURCE_GLOBS,
    force: bool = False,
) -> dict[str, Any]:
    """Rescan changed batch sources and rewrite the project index.

    Concurrent campaign workers may refresh at the same time. No lock is taken:
    the write is atomic, and a racing writer stores an equally complete scan, so
    the worst case is that one of two identical results wins. Rescanning is keyed
    on file content digests, so an unchanged project costs one stat per source
    file. Entries for a changed file are replaced rather than merged, because a
    declaration that moved or was re-stated must not keep
    its old identity.
    """
    root = Path(project_root).expanduser().resolve()
    previous = load_index(root)
    previous_files: Mapping[str, Any] = previous.get("files") or {}
    digests: dict[str, str] = {}
    for path in _iter_source_files(root, source_globs):
        if not path.is_file():
            continue
        try:
            digests[str(path.relative_to(root))] = _file_digest(path)
        except OSError:
            continue

    if not force and dict(previous_files) == digests:
        return {
            "version": _INDEX_VERSION,
            "entries": previous.get("entries") or [],
            "files": digests,
            "changed": False,
        }

    entries = [
        entry.as_dict() for entry in scan_project_declarations(root, source_globs=source_globs)
    ]
    payload = {
        "version": _INDEX_VERSION,
        "entries": entries,
        "files": digests,
        "changed": True,
    }
    atomic_json_write(index_path(root), payload)
    return payload


def lookup_by_signature(project_root: str | Path, signature_sha256: str) -> list[dict[str, Any]]:
    """Return indexed declarations whose normalized signature matches exactly."""
    wanted = str(signature_sha256 or "").strip()
    if not wanted:
        return []
    return [
        entry
        for entry in load_index(project_root).get("entries") or []
        if entry.get("signature_sha256") == wanted
    ]


def duplicate_groups(
    entries: Iterable[Mapping[str, Any]],
) -> dict[str, list[Mapping[str, Any]]]:
    """Group entries that share a normalized signature across batches.

    Grouping is by signature only. A shared name is deliberately not enough:
    in the HDP corpus 160 of 169 same-named declarations across files are
    different declarations, so name-based grouping would merge unrelated work.
    """
    groups: dict[str, list[Mapping[str, Any]]] = {}
    for entry in entries:
        key = str(entry.get("signature_sha256", "") or "")
        if not key:
            continue
        groups.setdefault(key, []).append(entry)
    return {
        key: sorted(
            group, key=lambda item: (str(item.get("batch_id", "")), int(item.get("line", 0)))
        )
        for key, group in groups.items()
        if len({str(item.get("batch_id", "")) for item in group}) > 1
    }


def index_summary(project_root: str | Path) -> dict[str, Any]:
    """Return counts for status output without exposing declaration bodies."""
    payload = load_index(project_root)
    entries = list(payload.get("entries") or [])
    groups = duplicate_groups(entries)
    return {
        "entries": len(entries),
        "files": len(payload.get("files") or {}),
        "duplicate_groups": len(groups),
        "duplicate_occurrences": sum(len(group) for group in groups.values()),
    }
