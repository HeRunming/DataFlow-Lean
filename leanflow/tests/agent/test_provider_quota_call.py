"""Exercise proof admission with fake network transports and a real quota ledger."""

from types import SimpleNamespace

import pytest

from agent.accounting.provider_quota import ProviderQuotaError
from agent.accounting.provider_quota_budget import (
    initialize_quota_budget,
    read_quota_budget,
    reserve_provider_request,
)
from agent.accounting.provider_quota_call import quota_chat_create, quota_chat_create_async
from tests.agent.test_provider_quota_budget import quota_env  # noqa: F401


@pytest.fixture
def guarded(monkeypatch, request):
    env = request.getfixturevalue("quota_env")
    for k, v in env.items():
        monkeypatch.setenv(k, v)
    initialize_quota_budget(env["LEANFLOW_PROVIDER_QUOTA_BUDGET_PATH"], limit_quota=10000)
    return env


def client_for(create):
    client = SimpleNamespace(base_url="https://api.zcloudapi.com/v1/")
    client.chat = SimpleNamespace(completions=SimpleNamespace(create=create))

    def options(**kwargs):
        assert kwargs == {"max_retries": 0}
        return client

    client.with_options = options
    return client


def request():
    return {
        "model": "gpt-6-astra",
        "messages": [{"role": "user", "content": "hello"}],
        "max_tokens": 5,
    }


def usage_response():
    return SimpleNamespace(usage=SimpleNamespace(prompt_tokens=49, completion_tokens=5))


def test_native_api_caller_reserves_before_network_and_settles(guarded):
    from agent.providers.api_caller import ApiCaller

    path = guarded["LEANFLOW_PROVIDER_QUOTA_BUDGET_PATH"]

    def create(**kwargs):
        assert read_quota_budget(path)["held_quota"] > 0
        return usage_response()

    client = client_for(create)
    agent = SimpleNamespace(
        api_mode="chat_completions",
        _delegate_depth=0,
        _interrupt_requested=False,
        _create_request_openai_client=lambda **kw: client,
        _close_request_openai_client=lambda *a, **kw: None,
        _provider_wait_heartbeat_seconds=lambda: 60,
    )
    ApiCaller(agent).interruptible_api_call(request())
    state = read_quota_budget(path)
    assert state["charges_quota"] == 82
    assert state["held_quota"] == 0


def test_quota_exhaustion_prevents_network(guarded, monkeypatch):
    monkeypatch.setenv("LEANFLOW_PROVIDER_QUOTA_SPEND_CEILING", "1")

    def forbidden(**kw):
        pytest.fail("provider was contacted without budget")

    with pytest.raises(ProviderQuotaError):
        quota_chat_create(client_for(forbidden), request())


def test_each_failed_retry_keeps_its_own_hold(guarded):
    def fail(**kw):
        raise TimeoutError("provider timed out")

    for _ in range(2):
        with pytest.raises(TimeoutError):
            quota_chat_create(client_for(fail), request())
    state = read_quota_budget(guarded["LEANFLOW_PROVIDER_QUOTA_BUDGET_PATH"])
    assert len(state["reservations"]) == 2
    assert all(r["status"] == "unknown" for r in state["reservations"].values())
    assert state["unknown_hold_quota"] > 0


def test_auxiliary_inherits_existing_statement_hold_without_double_charge(guarded, monkeypatch):
    reservation = reserve_provider_request(
        prompt="hello",
        system_prompt="",
        max_output_tokens=5,
        base_url="https://api.zcloudapi.com/v1",
        model="gpt-6-astra",
    )
    monkeypatch.setenv("LEANFLOW_PROVIDER_QUOTA_RESERVATION_ID", reservation.reservation_id)
    quota_chat_create(client_for(lambda **kw: usage_response()), request(), inherited=True)
    state = read_quota_budget(guarded["LEANFLOW_PROVIDER_QUOTA_BUDGET_PATH"])
    assert len(state["reservations"]) == 1
    assert state["charges_quota"] == 0
    reservation.settle(prompt_tokens=49, completion_tokens=5, status="ok")
    assert read_quota_budget(guarded["LEANFLOW_PROVIDER_QUOTA_BUDGET_PATH"])["charges_quota"] == 82
    with pytest.raises(ProviderQuotaError, match="does not match"):
        quota_chat_create(
            client_for(lambda **kw: pytest.fail("stale hold")), request(), inherited=True
        )


def test_missing_usage_preserves_hold(guarded):
    quota_chat_create(client_for(lambda **kw: SimpleNamespace()), request())
    assert (
        read_quota_budget(guarded["LEANFLOW_PROVIDER_QUOTA_BUDGET_PATH"])["unknown_hold_quota"] > 0
    )


@pytest.mark.parametrize("kwargs", [{}, {"max_tokens": 0}, {"max_tokens": 5, "stream": True}])
def test_unsupported_request_fails_closed(guarded, kwargs):
    with pytest.raises(ProviderQuotaError):
        quota_chat_create(
            client_for(lambda **kw: pytest.fail("invalid request")),
            {"model": "gpt-6-astra", **kwargs},
        )


@pytest.mark.asyncio
async def test_async_auxiliary_settles_shared_ledger(guarded):
    async def create(**kw):
        return usage_response()

    await quota_chat_create_async(client_for(create), request())
    assert read_quota_budget(guarded["LEANFLOW_PROVIDER_QUOTA_BUDGET_PATH"])["charges_quota"] == 82
