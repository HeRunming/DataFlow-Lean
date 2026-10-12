"""Recognize relay failures that arrive with a 4xx status but are really transient.

A 4xx normally means the request itself is wrong and retrying cannot help, so the
agent aborts on it. A New-API-style relay breaks that rule: when its upstream is
down it answers ``400`` with ``type: upstream_error`` and the message "服务可能有
问题，请稍后重试或重新发起请求" ("the service may have a problem, please retry"),
and when an account is over its concurrent-request cap it answers ``429`` with
``code: gateway_concurrency_limit``. Both are explicit invitations to retry.

Treating them as permanent made a proof worker on 2026-10-12 give up on its very
first call; the campaign then read that as a failed proof needing recovery and
stopped dispatching for hours. These checks are deliberately narrow: they match
the relay's own retry markers, not every 400, so a genuinely malformed request is
still rejected immediately.
"""

from __future__ import annotations

import re

# Markers the relay attaches only to failures it says are worth retrying.
_RELAY_RETRY_MARKERS = re.compile(
    r"upstream_error"
    r"|gateway_concurrency_limit"
    r"|concurrency limit exceeded"
    r"|请稍后重试"
    r"|重新发起请求"
    r"|retry shortly"
    r"|please retry later",
    re.IGNORECASE,
)


def is_relay_transient_error(status_code: int | None, error_text: str) -> bool:
    """Return whether a 4xx error is the relay asking the caller to retry.

    ``401`` and ``403`` are never transient here: an invalid or exhausted key
    must fail fast so the key pool can drop it, whatever the message says.
    """
    if status_code in (401, 403):
        return False
    if status_code is not None and not 400 <= status_code < 500:
        return False
    return bool(_RELAY_RETRY_MARKERS.search(str(error_text or "")))
