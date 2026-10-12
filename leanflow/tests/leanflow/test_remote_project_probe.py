"""Keep unrelated remote jobs out of HDP recovery admission."""

import json
import shlex

from leanflow_cli.formalization.campaign_recovery import remote_project_probe_command


def test_remote_probe_scopes_cwd_and_argv(tmp_path, capsys):
    records = [
        (100001, ["python3", "worker.py"], "/srv/lean/desynth"),
        (100002, ["lean", "Main.lean"], "/srv/lean/fate-x-work"),
        (100003, ["rsync", "--server", "/srv/lean/fate-x-work/"], "/home/lean"),
        (100004, ["python3", "worker.py"], "/srv/lean/fate-x-work-other"),
    ]
    for pid, args, cwd in records:
        proc = tmp_path / str(pid)
        proc.mkdir()
        (proc / "cmdline").write_bytes("\0".join(args).encode())
        (proc / "cwd").symlink_to(cwd)
    command = remote_project_probe_command("/srv/lean/fate-x-work")
    script = shlex.split(command)[2].replace(
        "pathlib.Path('/proc')", f"pathlib.Path({str(tmp_path)!r})"
    )
    exec(compile(script, "probe", "exec"), {})
    result = json.loads(capsys.readouterr().out)
    assert result["checked"]
    assert sorted(result["busy_pids"]) == [100002, 100003]
