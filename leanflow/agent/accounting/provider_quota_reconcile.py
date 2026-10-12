"""Identify quota holds whose owning process died before settlement.

A reservation is written before dispatch and settled after the response. The
reserve/settle pair lives in the child process that performs the call, so a
hard kill between the two - a campaign child timeout, an operator interrupt, a
SIGKILL to the process group - leaves the record at ``reserved`` forever. The
hold is correct (the request may have reached the provider and may have been
billed) but its state is unprovable, and the bare ``reserved`` label makes an
abandoned hold indistinguishable from a request that is still in flight.

This module performs the narrow, auditable correction: for a hold whose
reserving process identity no longer matches a live process, replace
``reserved`` with ``unknown`` and record why. It never releases capacity and
never rewrites ``charged`` or already-``unknown`` records, so the conservative
total held quota is unchanged - relabeling is bookkeeping, not forgiveness.
"""

from __future__ import annotations

import os
import time
from dataclasses import dataclass
from datetime import datetime
from pathlib import Path
from typing import Any, Mapping

from agent.accounting.provider_quota import ProviderQuotaError
from agent.accounting.provider_quota_budget import (
    _budget_lock,
    _now,
    _read,
)
from core.utils import atomic_json_write

# A request may legitimately stay unsettled for the whole provider timeout
# window. Only holds older than this are eligible for relabeling, so an
# in-flight call is never mistaken for an abandoned one.
DEFAULT_MIN_AGE_S = 3600.0

OWNER_DEAD = "owner_process_not_live"
OWNER_REUSED = "owner_pid_reused_by_another_process"


@dataclass(frozen=True)
class ReconciliationOutcome:
    """Summarize one reconciliation pass without exposing ledger internals."""

    scanned: int
    orphaned: int
    relabeled_quota: int
    skipped_open_holds: int
    reason_counts: Mapping[str, int]

    @property
    def changed(self) -> bool:
        """Return whether this pass rewrote any reservation state."""
        return self.orphaned > 0


def _age_seconds(item: Mapping[str, Any], *, now_epoch: float) -> float | None:
    """Return seconds since the hold was created, or None when unreadable."""
    created = str(item.get("created_at", "") or "").strip()
    if not created:
        return None
    try:
        created_at = datetime.fromisoformat(created)
    except ValueError:
        return None
    if created_at.tzinfo is None:
        created_at = created_at.replace(tzinfo=datetime.now().astimezone().tzinfo)
    return max(0.0, now_epoch - created_at.timestamp())


def _orphan_reason(item: Mapping[str, Any], *, now_epoch: float, min_age_s: float) -> str | None:
    """Classify one open hold, or return None when it must be left alone.

    Two conditions are required. The hold must be old enough that a request
    under the provider timeout cannot still be in flight, and its recorded
    process must be gone. Holds written before the ledger recorded a process
    identity are skipped entirely: guessing about them is exactly the
    unfounded release this ledger's policy forbids.
    """
    pid = _positive_int(item.get("process_id"))
    if pid <= 0:
        return None
    age = _age_seconds(item, now_epoch=now_epoch)
    if age is None or age < min_age_s:
        return None
    if _recorded_process_is_live(item, pid=pid):
        return None
    return OWNER_REUSED if _pid_is_taken(pid) else OWNER_DEAD


def _positive_int(value: Any) -> int:
    """Return a non-negative int for a persisted ledger field."""
    try:
        parsed = int(value)
    except (TypeError, ValueError):
        return 0
    return parsed if parsed > 0 else 0


def _pid_is_taken(pid: int) -> bool:
    """Return whether some live process currently holds this pid."""
    try:
        os.kill(pid, 0)
    except ProcessLookupError:
        return False
    except (AttributeError, PermissionError, OSError):
        # A permission error means the pid exists but is not ours to signal.
        return True
    return True


def _recorded_process_is_live(item: Mapping[str, Any], *, pid: int) -> bool:
    """Return whether the recorded owner process is still the one running.

    The recorded group and session pin the pid to the launch that wrote this
    hold. A live pid whose group no longer matches is a recycled pid running
    some unrelated process, so it must not be mistaken for the owner.
    """
    if not _pid_is_taken(pid):
        return False
    recorded_group = _positive_int(item.get("process_group_id"))
    recorded_session = _positive_int(item.get("process_session_id"))
    try:
        if recorded_group and os.getpgid(pid) != recorded_group:
            return False
        if recorded_session and os.getsid(pid) != recorded_session:
            return False
    except (AttributeError, ProcessLookupError, PermissionError, OSError):
        return False
    return True


def reconcile_orphaned_reservations(
    path: str | Path,
    *,
    min_age_s: float = DEFAULT_MIN_AGE_S,
    now_epoch: float | None = None,
    apply: bool = False,
) -> ReconciliationOutcome:
    """Relabel provably orphaned holds as unknown; never release quota.

    Runs read-only unless ``apply`` is set. Relabeling preserves the hold's
    ``reserved_quota`` and therefore leaves ``held_quota`` and
    ``remaining_quota`` untouched, matching the conservative accounting policy:
    an unsettled request is never treated as free.
    """
    if min_age_s < 0:
        raise ProviderQuotaError("orphan reconciliation requires a non-negative age floor")
    current_epoch = time.time() if now_epoch is None else float(now_epoch)
    resolved = Path(path).expanduser().resolve()
    reasons: dict[str, int] = {}
    scanned = 0
    orphaned = 0
    relabeled_quota = 0
    with _budget_lock(resolved):
        state = _read(resolved)
        for item in state["reservations"].values():
            if not isinstance(item, dict):
                continue
            scanned += 1
            if item.get("status") != "reserved":
                continue
            reason = _orphan_reason(item, now_epoch=current_epoch, min_age_s=min_age_s)
            if reason is None:
                continue
            reasons[reason] = reasons.get(reason, 0) + 1
            orphaned += 1
            relabeled_quota += int(item.get("reserved_quota", 0) or 0)
            if not apply:
                continue
            item["reconciled_from"] = item.get("status")
            item["status"] = "unknown"
            item["reconciled_at"] = _now()
            item["reconciliation_reason"] = reason
            item["reconciliation_note"] = (
                "reserving process did not outlive its request; the hold is "
                "retained because provider usage for this request is unknown"
            )
        if apply and orphaned:
            atomic_json_write(resolved, state)
    return ReconciliationOutcome(
        scanned=scanned,
        orphaned=orphaned,
        relabeled_quota=relabeled_quota,
        skipped_open_holds=0,
        reason_counts=reasons,
    )
