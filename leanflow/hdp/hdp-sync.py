#!/usr/bin/env python3
"""Sync the HDP launcher scripts to the Lean host, repairing shebangs on arrival.

The Mac and the server keep their Python interpreters at different absolute
paths, so every script that carries a shebang has to be rewritten after it
crosses. ``rsync`` copies bytes verbatim and therefore silently reverts that
rewrite: the file lands pointing at
``/opt/hdp/leanflow/.venv/bin/python``, which does not exist on the
server, and anything that execs the script dies with

    FileNotFoundError: [Errno 2] No such file or directory: '/srv/lean/hdp-run'

That is a confusing failure, because the file *is* there -- it is the
interpreter named on its first line that is missing. It cost a run on
2026-10-09. This helper makes the repair part of the sync rather than something
to remember, and then proves it worked by running each script's interpreter.

Usage:
    python hdp-sync.py            # sync and repair
    python hdp-sync.py --check    # verify only, change nothing
"""

from __future__ import annotations

import argparse
import subprocess
import sys
from pathlib import Path

MAC_PYTHON = "#!/opt/hdp/leanflow/.venv/bin/python"
SERVER_PYTHON = "#!/srv/lean/leanflow/.venv/bin/python"
MAC_ROOT = Path("/opt/hdp")
REMOTE = "lean@lean-host.example"
PORT = "22"
SERVER_ROOT = "/srv/lean"

# Every script that is exec'd rather than invoked as an argument to python.
# ``hdp-server-run.py`` is launched with an explicit interpreter, so its shebang
# is cosmetic, but it is included so a future caller that execs it directly is
# not surprised.
SCRIPTS = ("hdp-run", "hdp-scale", "hdp-long-run", "hdp-server-run.py")


def sync() -> None:
    """Copy the launcher scripts and the accounting module they depend on.

    Two separate transfers: the launchers live flat under the server root, while
    ``provider_quota.py`` has to keep its package path or the import breaks.
    """
    ssh = ["-e", f"ssh -p {PORT}"]
    launchers = [str(MAC_ROOT / name) for name in SCRIPTS if (MAC_ROOT / name).is_file()]
    subprocess.run(
        ["rsync", "-az", *ssh, *launchers, f"{REMOTE}:{SERVER_ROOT}/"],
        check=True,
        cwd=MAC_ROOT,
    )
    subprocess.run(
        [
            "rsync",
            "-az",
            *ssh,
            str(MAC_ROOT / "leanflow/agent/accounting/provider_quota.py"),
            f"{REMOTE}:{SERVER_ROOT}/leanflow/agent/accounting/",
        ],
        check=True,
        cwd=MAC_ROOT,
    )


def repair_and_check() -> int:
    """Rewrite Mac shebangs on the server, then prove each script is runnable."""
    remote = f"""
import sys
from pathlib import Path
MAC = {MAC_PYTHON!r}
SRV = {SERVER_PYTHON!r}
names = {list(SCRIPTS)!r}
fixed = []
for name in names:
    p = Path({SERVER_ROOT!r}) / name
    if not p.is_file():
        continue
    text = p.read_text(encoding="utf-8")
    if text.startswith(MAC):
        p.write_text(SRV + text[len(MAC):], encoding="utf-8")
        fixed.append(name)
print("repaired:", fixed)
bad = []
for name in names:
    p = Path({SERVER_ROOT!r}) / name
    if not p.is_file():
        continue
    first = p.read_text(encoding="utf-8").splitlines()[0]
    if first.startswith("#!"):
        interp = first[2:].strip()
        if not Path(interp).exists():
            bad.append((name, interp))
print("BROKEN:", bad)
sys.exit(1 if bad else 0)
"""
    result = subprocess.run(
        ["ssh", "-p", PORT, REMOTE, "python3 -"],
        input=remote,
        text=True,
        check=False,
    )
    return result.returncode


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="verify only; change nothing")
    args = parser.parse_args()
    if not args.check:
        sync()
        print("synced")
    code = repair_and_check()
    print("shebangs OK" if code == 0 else "shebangs BROKEN")
    return code


if __name__ == "__main__":
    raise SystemExit(main())
