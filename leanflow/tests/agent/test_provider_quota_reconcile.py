"""Guard orphan-hold reconciliation without network, Lean, or provider calls."""

import json
import os
import subprocess
import sys
from datetime import UTC, datetime

import pytest

from agent.accounting.provider_quota import ProviderQuotaError
from agent.accounting.provider_quota_budget import (
    BUDGET_PATH_ENV,
    QUOTE_PATH_ENV,
    initialize_quota_budget,
    read_quota_budget,
    reserve_provider_request,
)
from agent.accounting.provider_quota_reconcile import (
    OWNER_DEAD,
    reconcile_orphaned_reservations,
)

_LIMIT = 10_000_000


@pytest.fixture
def quota_env(tmp_path):
    quote = tmp_path / "quote.json"
    quote.write_text(
        json.dumps(
            {
                "unit": "provider_quota",
                "base_url": "https://api.zcloudapi.com/v1",
                "model": "gpt-6-astra",
                "group": "GPT 蒸馏分组",
                "model_ratio": "0.6849315068493151",
                "group_ratio": "1.6",
                "completion_ratio": "5",
                "cache_read_ratio": "0.1",
                "pricing_version": "observed-version",
                "observed_at_utc": datetime.now(UTC).isoformat(),
            }
        )
    )
    budget = tmp_path / "budget.json"
    initialize_quota_budget(budget, limit_quota=_LIMIT)
    return {
        "budget": budget,
        BUDGET_PATH_ENV: str(budget),
        QUOTE_PATH_ENV: str(quote),
        "LEANFLOW_AUXILIARY_RETRY_COUNT": "0",
        "LEANFLOW_AUXILIARY_TIMEOUT_RETRY_COUNT": "0",
    }


def _reserve(env, **overrides):
    return reserve_provider_request(
        prompt=overrides.get("prompt", "hello"),
        system_prompt="review",
        max_output_tokens=overrides.get("max_output_tokens", 5),
        base_url="https://api.zcloudapi.com/v1",
        model="gpt-6-astra",
        environ=env,
        task=overrides.get("task", ""),
    )


def _holds(path):
    state = read_quota_budget(path)
    return {
        "charged": state["charges_quota"],
        "held": state["held_quota"],
        "unknown": state["unknown_hold_quota"],
        "remaining": state["remaining_quota"],
    }


def test_hold_records_the_reserving_process_identity(quota_env):
    reservation = _reserve(quota_env, task="statement_review")
    record = read_quota_budget(quota_env["budget"])["reservations"][reservation.reservation_id]
    assert record["process_id"] == os.getpid()
    assert record["process_group_id"] == os.getpgid(os.getpid())
    assert record["task"] == "statement_review"
    # The token is stored only as a fingerprint, never in the clear.
    assert len(record["process_token_sha256"]) == 64


def test_live_owner_hold_is_never_relabeled(quota_env):
    _reserve(quota_env)
    # Age is far past the floor, but this process is obviously still alive.
    outcome = reconcile_orphaned_reservations(quota_env["budget"], min_age_s=0.0, apply=True)
    assert outcome.orphaned == 0
    assert not outcome.changed


def test_dead_owner_hold_becomes_unknown_without_releasing_quota(quota_env):
    # A child process reserves a hold and exits without settling it, which is
    # exactly what a hard kill between reserve and settle leaves behind.
    script = (
        "from agent.accounting.provider_quota_budget import reserve_provider_request;"
        "reserve_provider_request("
        "prompt='x',system_prompt='y',max_output_tokens=5,"
        "base_url='https://api.zcloudapi.com/v1',model='gpt-6-astra')"
    )
    completed = subprocess.run(
        [sys.executable, "-c", script],
        env={
            **quota_env,
        },
        check=False,
        capture_output=True,
        text=True,
    )
    assert completed.returncode == 0, completed.stderr

    before = _holds(quota_env["budget"])
    outcome = reconcile_orphaned_reservations(quota_env["budget"], min_age_s=0.0, apply=True)
    after = _holds(quota_env["budget"])

    assert outcome.orphaned == 1
    assert outcome.reason_counts == {OWNER_DEAD: 1}
    # Relabeling is bookkeeping: total held capacity and admission headroom are
    # unchanged, and the hold simply moves from "reserved" into "unknown".
    assert after["held"] == before["held"]
    assert after["remaining"] == before["remaining"]
    assert after["charged"] == before["charged"]
    assert after["unknown"] == outcome.relabeled_quota
    assert before["unknown"] == 0

    state = read_quota_budget(quota_env["budget"])
    relabeled = [
        item
        for item in state["reservations"].values()
        if item.get("reconciliation_reason") == OWNER_DEAD
    ]
    assert len(relabeled) == 1
    assert relabeled[0]["status"] == "unknown"
    assert relabeled[0]["reconciled_from"] == "reserved"


def test_dry_run_reports_orphans_without_rewriting_the_ledger(quota_env):
    script = (
        "from agent.accounting.provider_quota_budget import reserve_provider_request;"
        "reserve_provider_request("
        "prompt='x',system_prompt='y',max_output_tokens=5,"
        "base_url='https://api.zcloudapi.com/v1',model='gpt-6-astra')"
    )
    subprocess.run(
        [sys.executable, "-c", script], env={**quota_env}, check=True, capture_output=True
    )
    before = _holds(quota_env["budget"])
    outcome = reconcile_orphaned_reservations(quota_env["budget"], min_age_s=0.0, apply=False)
    after = _holds(quota_env["budget"])
    assert outcome.orphaned == 1
    # A dry run must leave both the derived totals and the states untouched.
    assert after == before
    state = read_quota_budget(quota_env["budget"])
    assert all(item["status"] == "reserved" for item in state["reservations"].values())


def test_hold_inside_the_age_floor_is_left_alone(quota_env):
    _reserve(quota_env)
    # A zero-width floor already covers the live-owner case; a large floor must
    # also suppress a genuinely abandoned hold that is simply too young to judge.
    outcome = reconcile_orphaned_reservations(quota_env["budget"], min_age_s=3600.0, apply=True)
    assert outcome.orphaned == 0


def test_negative_age_floor_is_rejected(quota_env):
    with pytest.raises(ProviderQuotaError):
        reconcile_orphaned_reservations(quota_env["budget"], min_age_s=-1.0)


def test_legacy_hold_without_identity_is_never_relabeled(quota_env):
    """Holds written before this field existed stay exactly as they are."""
    reservation = _reserve(quota_env)
    path = quota_env["budget"]
    state = json.loads(path.read_text(encoding="utf-8"))
    record = state["reservations"][reservation.reservation_id]
    for key in (
        "process_id",
        "process_group_id",
        "process_session_id",
        "process_token_sha256",
    ):
        record.pop(key, None)
    path.write_text(json.dumps(state), encoding="utf-8")

    outcome = reconcile_orphaned_reservations(path, min_age_s=0.0, apply=True)
    assert outcome.orphaned == 0
    assert (
        json.loads(path.read_text(encoding="utf-8"))["reservations"][reservation.reservation_id][
            "status"
        ]
        == "reserved"
    )
