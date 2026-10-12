"""Guard native chat requests and auxiliary calls with the shared quota ledger."""

from __future__ import annotations

import json
import os
from collections.abc import Mapping
from typing import Any

from agent.accounting.provider_quota import ProviderQuotaError
from agent.accounting.provider_quota_budget import (
    BUDGET_PATH_ENV,
    QUOTE_PATH_ENV,
    QuotaReservation,
    read_quota_budget,
    reserve_provider_request,
)


def quota_enabled() -> bool:
    """Fail closed when either half of the quota configuration is present."""
    return bool(os.getenv(BUDGET_PATH_ENV) or os.getenv(QUOTE_PATH_ENV))


def _reserve(
    client: Any,
    kwargs: Mapping[str, Any],
    *,
    inherited: bool,
    task: str = "",
) -> QuotaReservation | None:
    """Reserve the entire wire payload, including tools, before any network call."""
    if not quota_enabled():
        return None
    if kwargs.get("stream"):
        raise ProviderQuotaError("quota-gated chat calls require a non-streaming usage receipt")
    cap = kwargs.get("max_completion_tokens", kwargs.get("max_tokens"))
    if isinstance(cap, bool) or not isinstance(cap, int) or cap <= 0:
        raise ProviderQuotaError("quota-gated calls require an explicit positive output cap")
    base_url = str(client.base_url).rstrip("/")
    model = str(kwargs.get("model") or "")
    reservation_id = os.getenv("LEANFLOW_PROVIDER_QUOTA_RESERVATION_ID", "") if inherited else ""
    if reservation_id:
        # The bounded statement parent owns settlement. Never trust an ID
        # alone: a stale/mismatched hold must not bypass admission.
        if not os.getenv(BUDGET_PATH_ENV) or not os.getenv(QUOTE_PATH_ENV):
            raise ProviderQuotaError("inherited quota hold requires budget and quote paths")
        record = read_quota_budget(os.environ[BUDGET_PATH_ENV])["reservations"].get(
            reservation_id, {}
        )
        if not (
            record.get("status") == "reserved"
            and record.get("base_url", "").rstrip("/") == base_url
            and record.get("model") == model
            and cap <= record.get("completion_token_bound", record.get("max_output_tokens", 0))
        ):
            raise ProviderQuotaError("inherited quota reservation does not match this request")
        return None
    return reserve_provider_request(
        prompt=json.dumps(dict(kwargs), ensure_ascii=False, default=str),
        system_prompt="",
        max_output_tokens=cap,
        base_url=base_url,
        model=model,
        task=task,
    )


def _settle(reservation: QuotaReservation | None, response: Any) -> None:
    """Charge known usage; preserve a hold when the response omits usage."""
    if reservation is None:
        return
    usage = getattr(response, "usage", None)

    def field(name: str) -> Any:
        return usage.get(name, 0) if isinstance(usage, Mapping) else getattr(usage, name, 0)

    reservation.settle(
        prompt_tokens=field("prompt_tokens"),
        completion_tokens=field("completion_tokens"),
        status="ok",
    )


def quota_chat_create(client: Any, kwargs: dict[str, Any], *, inherited: bool = False) -> Any:
    """Dispatch exactly one guarded request, retaining uncertainty on exceptions."""
    reservation = _reserve(client, kwargs, inherited=inherited)
    try:
        request_client = client.with_options(max_retries=0) if quota_enabled() else client
        response = request_client.chat.completions.create(**kwargs)
    except BaseException:
        if reservation is not None:
            reservation.settle(prompt_tokens=0, completion_tokens=0, status="exception")
        raise
    _settle(reservation, response)
    return response


async def quota_chat_create_async(
    client: Any, kwargs: dict[str, Any], *, inherited: bool = False
) -> Any:
    """Apply the same one-request admission contract to asynchronous auxiliaries."""
    reservation = _reserve(client, kwargs, inherited=inherited)
    try:
        request_client = client.with_options(max_retries=0) if quota_enabled() else client
        response = await request_client.chat.completions.create(**kwargs)
    except BaseException:
        if reservation is not None:
            reservation.settle(prompt_tokens=0, completion_tokens=0, status="exception")
        raise
    _settle(reservation, response)
    return response
