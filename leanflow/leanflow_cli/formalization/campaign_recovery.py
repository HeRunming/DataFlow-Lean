"""Archive and roll back failed proof edits after all campaign writers drain."""

from __future__ import annotations

import base64
import hashlib
import json
import os
import re
import shlex
import subprocess
from pathlib import Path
from typing import Any

from core.utils import atomic_json_write
from leanflow_cli.formalization.campaign_store import update_campaign_file
from leanflow_cli.formalization.corpus_campaign import release_campaign_lease
from leanflow_cli.formalization.proof_plan_recovery import capture_plan, restore_plan, validate_plan


def remote_project_probe_command(project: str) -> str:
    """Inspect only this project's remote writers, not unrelated Python jobs."""
    script = r"""
import json, os, pathlib
root = PROJECT_ROOT
busy = []
errors = []
for proc in pathlib.Path('/proc').iterdir():
    if not proc.name.isdigit() or int(proc.name) == os.getpid():
        continue
    try:
        if proc.stat().st_uid != os.getuid():
            continue
        args = (proc / 'cmdline').read_bytes().decode(errors='replace').split('\0')
        executable = pathlib.Path(args[0]).name if args else ''
        if executable not in {'lean', 'lake', 'repl', 'rsync', 'python', 'python3', 'python3.12', 'python3.11'}:
            continue
        cwd = os.readlink(proc / 'cwd')
        scoped = cwd == root or cwd.startswith(root + '/')
        scoped = scoped or any(a == root or a.startswith(root + '/') for a in args[1:])
        if scoped:
            busy.append(int(proc.name))
    except FileNotFoundError:
        continue
    except PermissionError:
        if proc.exists():
            errors.append(int(proc.name))
print(json.dumps({'checked': not errors, 'busy_pids': busy, 'errors': errors}))
""".replace("PROJECT_ROOT", repr(project))
    return "python3 -c " + shlex.quote(script)


def local_runtime_pids(output: str) -> list[int]:
    """Recognize executable arguments, excluding shell descriptions and grep text."""
    busy = []
    for line in output.splitlines():
        try:
            pid_text, command = line.strip().split(None, 1)
            args = shlex.split(command)
            pid = int(pid_text)
        except (ValueError, IndexError):
            continue
        if not args or pid == os.getpid():
            continue
        executable = Path(args[0]).name
        relevant = executable == "lake" and "remote-bin" in args[0]
        if re.fullmatch(r"python(?:\d+(?:\.\d+)*)?", executable):
            if "-m" in args:
                index = args.index("-m") + 1
                module = args[index] if index < len(args) else ""
                relevant = (
                    module.startswith("leanflow_cli.")
                    or module == "agent.providers.isolated_auxiliary"
                )
            else:
                relevant = any(
                    Path(a).name == "lean-probe-service.py"
                    for a in args[1:]
                    if not a.startswith("-")
                )
        if executable in {"bash", "sh"} and len(args) > 1:
            relevant = Path(args[1]).name == "lake" and "remote-bin" in args[1]
        if relevant:
            busy.append(pid)
    return sorted(busy)


def own_warm_probe_pids(output: str) -> list[int]:
    """Return the pids of warm-probe service processes in a ``ps`` listing.

    On a single host the orchestrator starts its own warm probe before dispatch
    and leaves it running, so a probe in the process table is normal rather than
    a sign of a competing run: counting it as busy made every restart refuse
    itself and killed the run seconds after it started. ``ps`` shows the service
    as a ``python3 -u <dir>/lean-probe-service.py`` argv (sometimes wrapped in
    ``timeout``), which is what this matches on.

    This excludes every probe process, not only the caller's own: each
    invocation uses a fresh random ``mktemp`` directory, so the listing carries
    no marker that would tell them apart. That leaves a competing orchestrator
    to be caught by the campaign's own controller lock and by its worker and
    ``lake`` processes, which this does not filter.
    """
    pids = []
    for line in output.splitlines():
        try:
            pid_text, command = line.strip().split(None, 1)
            args = shlex.split(command)
            pid = int(pid_text)
        except (ValueError, IndexError):
            continue
        if any(
            Path(arg).name == "lean-probe-service.py"
            for arg in args
            if not arg.startswith("-")
        ):
            pids.append(pid)
    return sorted(pids)


def _files(directory: Path) -> dict[str, bytes]:
    """Read only regular Lean sources without following directory symlinks."""
    result: dict[str, bytes] = {}
    if not directory.exists():
        return result
    if directory.is_symlink():
        raise ValueError("recovery directory is a symlink")
    for root, dirs, files in os.walk(directory, followlinks=False):
        if any((Path(root) / name).is_symlink() for name in dirs):
            raise ValueError("recovery subtree contains a directory symlink")
        for name in files:
            p = Path(root) / name
            if p.suffix != ".lean":
                continue
            if p.is_symlink():
                raise ValueError("recovery subtree contains a source symlink")
            result[str(p.relative_to(directory))] = p.read_bytes()
    return result


def capture_proof_snapshot(
    target: Path, project: Path, destination: Path, *, batch_id: str | None = None
) -> dict[str, str]:
    """Save exact pre-action bytes so a failed proof can be deferred without data loss."""
    project = project.resolve()
    target = target.absolute()
    if not target.is_relative_to(project) or target.resolve() != target or not target.is_file():
        raise ValueError("proof snapshot requires a regular project-local target")
    payload = {
        "target": str(target),
        "project": str(project),
        "files": {
            name: base64.b64encode(data).decode() for name, data in _files(target.parent).items()
        },
    }
    if batch_id is not None:
        payload["plan"] = capture_plan(project, batch_id)
    atomic_json_write(destination, payload)
    return {
        "path": str(destination),
        "sha256": hashlib.sha256(destination.read_bytes()).hexdigest(),
    }


def restore_failed_proof(
    item: dict[str, Any], batch: dict[str, Any], *, project: Path
) -> dict[str, Any]:
    """Archive failed edits and restore the snapshot; callers must first prove runtime idle."""
    reference = item.get("proof_snapshot", {})
    path = Path(reference.get("path", ""))
    raw = path.read_bytes()
    if hashlib.sha256(raw).hexdigest() != reference.get("sha256"):
        raise ValueError("proof snapshot digest mismatch")
    snapshot = json.loads(raw)
    target = Path(snapshot["target"])
    if (
        snapshot["project"] != str(project.resolve())
        or str(target) != item.get("target_path")
        or not target.is_relative_to(project.resolve())
        or target.resolve() != target
    ):
        raise ValueError("proof snapshot scope mismatch")
    if batch.get("lease"):
        raise ValueError("proof still leased")
    if batch.get("status") in {"proofs_completed", "completed"}:
        raise ValueError("cannot restore over a completed proof")
    # A changed attempt ledger is legitimate only when this exact worker wrote
    # failure receipts. Never overwrite a different worker's or a successful result.
    attempts = batch.get("attempts", [])
    prior = item.get("attempts_before", len(attempts))
    before_hash = item.get("attempts_before_sha256")
    if (
        before_hash
        and hashlib.sha256(json.dumps(attempts[:prior], sort_keys=True).encode()).hexdigest()
        != before_hash
    ):
        raise ValueError("pre-existing proof attempts changed")
    fresh = attempts[prior:]
    if any(a.get("success") or a.get("worker_id") != item.get("worker_id") for a in fresh):
        raise ValueError("another or successful attempt changed the proof ledger")
    expected = {
        name: base64.b64decode(data, validate=True) for name, data in snapshot["files"].items()
    }
    for name in expected:
        relative = Path(name)
        if relative.is_absolute() or ".." in relative.parts or relative.suffix != ".lean":
            raise ValueError("invalid snapshot source path")
    current = _files(target.parent)
    # Validate plan state and archive it before touching sources. New runs
    # restore both sides of the handoff; legacy runs rebuild from source.
    plan_snapshot = snapshot.get("plan", {"batch_id": item["batch_id"], "files": {}})
    expected_plan = validate_plan(plan_snapshot, item["batch_id"])
    current_plan = capture_plan(project, item["batch_id"])
    plan_archive = path.with_name(path.stem + "-failed-plan.json")
    if not plan_archive.exists():
        atomic_json_write(plan_archive, current_plan)
    archive = path.with_name(path.stem + "-failed.json")
    if not archive.exists():
        atomic_json_write(
            archive,
            {
                "batch_id": item["batch_id"],
                "target": str(target),
                "snapshot_sha256": reference["sha256"],
                "files": {name: base64.b64encode(data).decode() for name, data in current.items()},
            },
        )
    # Archive is durable before any mutation. A repeated call resumes the same
    # transaction, preserving the original candidate even after a partial restore.
    for name, content in expected.items():
        p = target.parent / name
        p.parent.mkdir(parents=True, exist_ok=True)
        temp = p.with_suffix(".lean.recovery-tmp")
        temp.write_bytes(content)
        temp.replace(p)
    for name in current.keys() - expected.keys():
        (target.parent / name).unlink()
    if _files(target.parent) != expected:
        raise RuntimeError("restored proof differs from its snapshot")
    plan_result = restore_plan(project, item["batch_id"], expected_plan, archive=plan_archive)
    plan_result["legacy_reset"] = "plan" not in snapshot
    return {
        "archive": str(archive),
        "snapshot": str(path),
        "restored": True,
        "source_changed": current != expected,
        "target": str(target),
        "plan": plan_result,
    }


def compile_restored_target(target: Path, *, project: Path, lake: Path) -> dict[str, Any]:
    """Require remote Lake compilation of restored bytes without claiming proof completion."""
    env = dict(os.environ, LEANFLOW_REMOTE_LEAN_TIMEOUT_S="120")
    result = subprocess.run(
        [str(lake), "env", "lean", str(target)],
        cwd=project,
        env=env,
        capture_output=True,
        text=True,
        timeout=150,
    )
    return {
        "ok": result.returncode == 0,
        "exit_code": result.returncode,
        "diagnostic": (result.stdout + result.stderr)[-4000:],
    }


def reconcile_wave(
    state: dict[str, Any],
    campaign: Path,
    *,
    project: Path,
    runtime: dict[str, Any],
    compile_target: Any,
) -> bool:
    """Quarantine failed proofs only after writers exit and restored sources compile."""
    if state.get("active"):
        return False
    if not all(runtime.get(k) is True for k in ("checked", "local_idle", "remote_idle")):
        state["recovery_wait"] = {
            "reason": "writers_or_runtime_probe",
            "runtime": runtime,
        }
        return False

    def release_orphans(current: Any) -> tuple[Any, list[str]]:
        released = []
        for item in state.get("items", []):
            if item.get("exit_code") is None:
                continue
            owner = item.get("observed_worker_id") or item.get("worker_id")
            batch: dict[str, Any] = next(
                (b for b in current["batches"] if b["id"] == item["batch_id"]), {}
            )
            lease = batch.get("lease", {})
            if (
                owner
                and lease.get("worker_id") == owner
                and lease.get("stage") == item.get("stage")
            ):
                current = release_campaign_lease(
                    current, batch_id=item["batch_id"], worker_id=owner
                )
                item["lease_after"] = None
                released.append(item["batch_id"])
        return current, released

    released = update_campaign_file(campaign, release_orphans)
    if released:
        state.setdefault("released_orphan_leases", []).extend(released)
    batches = {b["id"]: b for b in json.loads(campaign.read_text())["batches"]}
    if any(b.get("lease") for b in batches.values()):
        state["recovery_wait"] = {"reason": "leases_remaining"}
        return False
    for item in state.get("items", []):
        if item.get("classification") == "accepted" or item.get("safe_to_continue"):
            continue
        if item.get("stage") != "proofs":
            if not item.get("new_attempts"):
                state["recovery_wait"] = {
                    "reason": "statement_receipt_missing",
                    "batch_id": item["batch_id"],
                }
                return False
            continue
        try:
            if not item.get("proof_snapshot"):
                if item.get("receipt_recovery", {}).get("safe_to_retry"):
                    item["safe_to_continue"] = True
                    continue
                raise ValueError("failed proof lacks a recoverable source snapshot")
            restored = restore_failed_proof(item, batches[item["batch_id"]], project=project)
            item["restoration"] = restored
            checked = compile_target(Path(restored["target"]))
            item["restoration_check"] = checked
            if not checked.get("ok"):
                state["recovery_wait"] = {
                    "reason": "restored_compile_unavailable",
                    "batch_id": item["batch_id"],
                }
                return False
        except (OSError, ValueError, RuntimeError, subprocess.SubprocessError) as exc:
            state["recovery_wait"] = {
                "reason": "proof_restore_pending",
                "batch_id": item["batch_id"],
                "error_type": type(exc).__name__,
                "error": str(exc)[:500],
            }
            return False
        item["safe_to_continue"] = True
        item["receipt_recovery"] = {
            "safe_to_retry": False,
            "safe_to_continue": True,
            "disposition": "archived_restored_and_deferred",
            "manual_reconciliation_required": False,
        }
    state.pop("recovery_wait", None)
    return True


def dependent_exclusions(campaign: Path, excluded: set[str]) -> set[str]:
    """Defer transitive consumers of quarantined batches for this supervisor run."""
    batches = json.loads(campaign.read_text())["batches"]
    result = set(excluded)
    while True:
        labels = {str(label) for b in batches if b["id"] in result for label in b.get("labels", [])}
        consumers = {
            b["id"]
            for b in batches
            if labels.intersection(
                str(label)
                for key in ("dependency_labels", "soft_dependency_labels")
                for label in b.get(key, [])
            )
        }
        updated = result | consumers
        if updated == result:
            return result
        result = updated
