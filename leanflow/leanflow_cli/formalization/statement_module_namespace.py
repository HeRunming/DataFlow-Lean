"""Give every generated statement file a namespace no other item file can share.

Each campaign item becomes one ``Main.lean`` module, and the project root imports
all of them into a single environment. Lean rejects that import outright when two
modules define the same top-level name, so independently generated files collide
on ordinary helper names: on 2026-10-10 the root refused
``environment already contains 'euclideanNorm'`` and ``'sourceEuclideanNorm'``,
and those statements -- compiled, reviewed and accepted -- could never be
integrated or proved. Across the corpus 26 such names were already shared, and 18
not-yet-integrated files were blocked by a name the root already held.

A model-chosen namespace does not solve this: ``Source`` alone is reused by ten
files. The namespace here is derived from the module path, which is unique per
item by construction, so no prompt compliance is required.

Wrapping is idempotent and leaves the header -- imports, ``open``, ``set_option``,
``universe`` -- outside the namespace, where Lean requires imports to stay.
"""

from __future__ import annotations

import re
from pathlib import Path

_HEADER_LINE_RE = re.compile(r"^\s*(?:import\b|open\b|set_option\b|universe\b|--|/-|$)")


def module_namespace(target_relative: str | Path) -> str:
    """Return the Lean namespace reserved for one generated module.

    ``FateXWork/Environments/Items730E8281E0/Main.lean`` maps to
    ``HDPItem.Items730E8281E0``. The item directory name is already a stable,
    hash-suffixed identifier, which is what makes the namespace collision-free.
    """
    parts = Path(str(target_relative)).with_suffix("").parts
    item = parts[-2] if len(parts) >= 2 and parts[-1] == "Main" else parts[-1]
    item = re.sub(r"[^A-Za-z0-9_]", "_", item)
    if not re.match(r"[A-Za-z_]", item):
        item = f"M{item}"
    return f"HDPItem.{item}"


def _strip_block_comment_prefix(lines: list[str], start: int) -> int:
    """Return the index after a leading ``/- ... -/`` block beginning at ``start``."""
    depth = 0
    for index in range(start, len(lines)):
        depth += lines[index].count("/-") - lines[index].count("-/")
        if depth <= 0:
            return index + 1
    return len(lines)


def wrap_in_module_namespace(lean_code: str, namespace: str) -> str:
    """Wrap a statement file's declarations in ``namespace``, keeping the header outside.

    The header is the leading run of imports, ``open``/``set_option``/``universe``
    commands, comments and blank lines. Everything after it moves inside the
    namespace, including any namespace the model opened itself, so its own names
    become ``namespace.Model.name`` and still cannot collide. A file already
    wrapped in this exact namespace is returned unchanged.
    """
    if re.search(rf"(?m)^namespace\s+{re.escape(namespace)}\s*$", lean_code):
        return lean_code
    lines = lean_code.splitlines()
    index = 0
    while index < len(lines):
        line = lines[index]
        if line.lstrip().startswith("/-"):
            index = _strip_block_comment_prefix(lines, index)
            continue
        if not _HEADER_LINE_RE.match(line):
            break
        index += 1
    header = "\n".join(lines[:index]).rstrip()
    body = "\n".join(lines[index:]).strip()
    if not body:
        return lean_code
    wrapped = f"namespace {namespace}\n\n{body}\n\nend {namespace}\n"
    return f"{header}\n\n{wrapped}" if header else wrapped
