"""Render the shared-vocabulary list for prover and planner prompts.

Each batch is formalized in isolation, so a prover that needs a Euclidean norm
has no way to know one already exists elsewhere in the corpus and defines its
own. The HDP corpus shows the cost directly: ``euclideanNorm`` was written 29
times in 9 distinct shapes.

This module turns the read-only declaration index into a short prompt block that
tells the prover which shared vocabulary already exists. It is deliberately
advisory: the prover still decides, and nothing here edits a file, opens a
graph, or spends quota. The block is bounded, because an index entry list grows
with the corpus and a prompt must not.
"""

from __future__ import annotations

import os
from collections.abc import Mapping
from pathlib import Path
from typing import Any

from leanflow_cli.formalization import corpus_shared_index

MAX_LISTED_DECLARATIONS = 24
HEADER = "[LEANFLOW SHARED VOCABULARY]"


def _module_for_entry(entry: Mapping[str, Any]) -> str:
    """Return the Lean name prefix that actually reaches one declaration.

    The enclosing namespace is preferred over the module name: a file at
    ``FateXWork/Environments/Shared/Analysis.lean`` is module
    ``FateXWork.Environments.Shared.Analysis`` but may declare its symbols in
    ``FateXWork.Shared.Analysis``, and only the latter resolves. The module name
    is the fallback for a declaration that sits outside any namespace.
    """
    namespace = str(entry.get("namespace", "") or "").strip()
    if namespace:
        return namespace
    file_name = str(entry.get("file", "") or "")
    return ".".join(Path(file_name).with_suffix("").parts)


def _shared_modules(entries: list[Mapping[str, Any]]) -> list[tuple[str, list[str]]]:
    """Group indexed declarations by the name prefix that reaches them.

    Only declarations living in the shared tree are listed -- a batch's own file
    is not vocabulary to reuse. The prefix is rendered in full because a planner
    may copy it straight into Lean, where an abbreviated form does not resolve.
    """
    grouped: dict[str, list[str]] = {}
    for entry in entries:
        file_name = str(entry.get("file", "") or "")
        if "Shared" not in Path(file_name).parts:
            continue
        module = _module_for_entry(entry)
        name = str(entry.get("name", "") or "")
        if not module or not name:
            continue
        grouped.setdefault(module, [])
        if name not in grouped[module]:
            grouped[module].append(name)
    return sorted((module, sorted(names)) for module, names in grouped.items())


def _resolved_project_root(project_root: str | Path | None) -> Path | None:
    """Return the project root for index lookup, or None when it is unknown.

    Prompt assembly helpers in this package are argument-free and read their
    paths from the environment, so the environment is the default source and an
    explicit argument exists only for tests and callers that already hold it.
    """
    if project_root is not None:
        return Path(project_root).expanduser()
    raw = str(os.getenv("LEANFLOW_PROJECT_ROOT", "") or "").strip()
    return Path(raw).expanduser() if raw else None


def prompt_block(project_root: str | Path | None = None) -> str:
    """Return a bounded prompt block naming already-defined shared declarations.

    An unknown project, an unbuilt index, or an index with nothing to say all
    return the empty string, so callers can concatenate unconditionally.
    """
    root = _resolved_project_root(project_root)
    if root is None:
        return ""
    try:
        payload = corpus_shared_index.load_index(root)
    except Exception:
        return ""
    entries = [entry for entry in payload.get("entries") or [] if isinstance(entry, Mapping)]
    modules = _shared_modules(entries)
    if not modules:
        return ""

    lines = [
        HEADER,
        "These declarations already exist in the project's shared modules.",
        "Import the shared module instead of redefining them:",
    ]
    listed = 0
    for module, names in modules:
        if listed >= MAX_LISTED_DECLARATIONS:
            break
        remaining = MAX_LISTED_DECLARATIONS - listed
        shown = names[:remaining]
        listed += len(shown)
        suffix = "" if len(shown) == len(names) else f" (+{len(names) - len(shown)} more)"
        lines.append(f"- `{module}`: {', '.join(shown)}{suffix}")
    lines.append(
        "If a definition you need is listed, import it. Only define a new shared "
        "object when no listed declaration matches the statement you need."
    )
    return "\n".join(lines)


def summary(project_root: str | Path | None = None) -> dict[str, Any]:
    """Return counts for status output without rendering the prompt block."""
    root = _resolved_project_root(project_root)
    if root is None:
        return {"entries": 0, "duplicate_groups": 0}
    try:
        return dict(corpus_shared_index.index_summary(root))
    except Exception:
        return {"entries": 0, "duplicate_groups": 0}
