"""Single source of truth for the LeanFlow home directory.

This lives in ``core/`` — the lowest layer — so the session store (:mod:`core.state`), the
clock (:mod:`core.time`) and the ``tools/`` data stores (checkpoints, memories, skills) can all
resolve the home *without* importing the higher ``leanflow_cli`` package.

The home is ``~/.leanflow``, overridable with the ``LEANFLOW_HOME`` env var. The CLI entrypoints
set ``LEANFLOW_HOME`` before anything reads state, so a plain ``getenv`` is enough here.
"""

from __future__ import annotations

import os
import tempfile
from pathlib import Path

HOME_ENV = "LEANFLOW_HOME"
DEFAULT_HOME = Path.home() / ".leanflow"


def leanflow_home() -> Path:
    """Return the active LeanFlow home (``$LEANFLOW_HOME`` or ``~/.leanflow``)."""
    explicit = os.getenv(HOME_ENV, "").strip()
    return Path(explicit).expanduser() if explicit else DEFAULT_HOME


def scratch_root() -> Path:
    """Return the directory for short-lived runtime files (sockets, shell IPC, bg logs).

    Defaults to the system temp dir, which is right on a normal host. It is
    overridable because the default can be on a filesystem with no room: the
    shared Lean host has a 100%-full root volume with ``/tmp`` on it, and a
    probe failure there once presented as "No space left on device" on every
    attempt. Setting ``LEANFLOW_SCRATCH_ROOT`` moves these files to a volume
    with space, which matters because some of them (the SSH ControlMaster
    socket, the persistent shell's exit-code files) are written on *every*
    command and fail in ways that look like logic errors, not disk errors.
    """
    override = str(os.getenv("LEANFLOW_SCRATCH_ROOT", "") or "").strip()
    if override:
        return Path(override).expanduser()
    return Path("/tmp") if Path("/tmp").is_dir() else Path(tempfile.gettempdir())
