"""Test deterministic local Lean toolchain discovery."""

from leanflow_cli.runtime.toolchain_env import add_lean_toolchain_env, discover_lean_bin


def test_discovers_workspace_ancestor_elan_home(tmp_path):
    project = tmp_path / "workspace" / "project"
    lean_bin = tmp_path / "workspace" / ".elan-home" / "bin"
    project.mkdir(parents=True)
    lean_bin.mkdir(parents=True)
    for name in ("lake", "lean"):
        executable = lean_bin / name
        executable.write_text("#!/bin/sh\n", encoding="utf-8")
        executable.chmod(0o755)

    discovered = discover_lean_bin(project, environ={"PATH": ""})
    child_env = add_lean_toolchain_env(
        {"PATH": "/usr/bin"}, project_root=project, environ={"PATH": ""}
    )

    assert discovered == lean_bin
    assert child_env["PATH"].split(":")[0] == str(lean_bin)
    assert child_env["ELAN_HOME"] == str(lean_bin.parent)


def test_skips_a_toolchain_that_cannot_run_on_this_host(tmp_path, monkeypatch):
    """A foreign-platform toolchain must not be selected just for having exec bits.

    A macOS-ARM ``.elan-home`` inside the project shadowed the working Linux
    toolchain: ``os.access(..., X_OK)`` was true, so discovery returned it and
    every statement candidate died in ``lake`` with "Exec format error (os
    error 8)". The check has to be "does this format run here", not "is the exec
    bit set".
    """
    project = tmp_path / "workspace" / "project"
    foreign = tmp_path / "workspace" / ".elan-home" / "bin"
    project.mkdir(parents=True)
    foreign.mkdir(parents=True)
    for name in ("lake", "lean"):
        executable = foreign / name
        # A Mach-O 64-bit little-endian header: executable on macOS, not on Linux.
        executable.write_bytes(b"\xcf\xfa\xed\xfe" + b"\x00" * 32)
        executable.chmod(0o755)

    monkeypatch.setattr("sys.platform", "linux")
    assert discover_lean_bin(project, environ={"PATH": ""}) is None


def test_accepts_a_shell_script_toolchain(tmp_path):
    """The project's own remote-bin wrapper is a #! script and must still qualify."""
    project = tmp_path / "workspace" / "project"
    lean_bin = tmp_path / "workspace" / ".elan-home" / "bin"
    project.mkdir(parents=True)
    lean_bin.mkdir(parents=True)
    for name in ("lake", "lean"):
        executable = lean_bin / name
        executable.write_text("#!/bin/sh\n", encoding="utf-8")
        executable.chmod(0o755)

    assert discover_lean_bin(project, environ={"PATH": ""}) == lean_bin
