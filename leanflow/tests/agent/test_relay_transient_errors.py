"""Cover the relay errors that carry a 4xx status but ask to be retried."""

from __future__ import annotations

import pytest

from agent.providers.relay_transient_errors import is_relay_transient_error

# Exact bodies observed from the relay on 2026-10-12, lowercased the way
# run_agent passes them.
UPSTREAM_400 = (
    "error code: 400 - {'error': {'message': '服务可能有问题，请稍后重试或重新发起请求 "
    "(request id: x)', 'type': 'upstream_error', 'param': '', 'code': 'upstream_error'}}"
)
CONCURRENCY_429 = (
    "error code: 429 - {'error': {'message': 'concurrency limit exceeded for user, please "
    "retry later', 'type': 'rate_limit_error', 'param': '', 'code': 'gateway_concurrency_limit'}}"
)


def test_relay_upstream_400_is_retried():
    """This one made a proof worker abort on its first call."""
    assert is_relay_transient_error(400, UPSTREAM_400)


def test_relay_concurrency_429_is_retried():
    assert is_relay_transient_error(429, CONCURRENCY_429)


@pytest.mark.parametrize("status", [401, 403])
def test_auth_failures_are_never_treated_as_transient(status):
    """A dead key must fail fast so the key pool can drop it."""
    assert not is_relay_transient_error(status, UPSTREAM_400)


def test_an_ordinary_bad_request_still_aborts():
    assert not is_relay_transient_error(
        400, "error code: 400 - {'error': {'message': 'invalid parameter: max_tokens'}}"
    )


def test_non_4xx_statuses_are_out_of_scope():
    """5xx is already retried by the generic path; this check only rescues 4xx."""
    assert not is_relay_transient_error(500, UPSTREAM_400)


def test_status_unknown_relies_on_the_relay_markers():
    assert is_relay_transient_error(None, UPSTREAM_400)
    assert not is_relay_transient_error(None, "connection reset by peer")
