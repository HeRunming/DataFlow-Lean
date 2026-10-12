"""Launch an HDP long run against the operator's new relay.

On 2026-10-08 the operator moved the campaign off zcloud onto a self-hosted
New-API relay at ``http://relay.example:3000`` and chose ``gpt-6-sol``. This
launcher is the production entry point for that provider; the zcloud-era scripts
(``hdp-server-launch.py``, ``hdp-server-topup-short.py``) are kept only as
history and must not be used, because their pinned base URL and model no longer
match what ``hdp-scale`` enforces.

Ledger discipline, unchanged:

* The 2026-10-06 source ledger is never rebuilt, reset, or edited. Its limit is
  immutable and its held and unknown reservations stay exactly as they are.
* Capacity comes from the existing 2026-10-08 ledger, which is reused as-is.
  ``initialize_quota_budget`` refuses to reset an existing limit, so no hold is
  released or re-labelled by starting a run.
* The provider quote is really fetched over the network here; no old quote is
  re-timestamped. Its group ratio is the relay's own ``default`` group.

Two provider facts this launcher has to state explicitly, both load-bearing:

* The relay serves **plain HTTP with no TLS listener on any port**, so quoting is
  refused unless ``LEANFLOW_ALLOW_INSECURE_QUOTA_ENDPOINT`` is set. That opt-in
  exists precisely so this is a decision someone made, not a default.
* ``gpt-6-sol`` is roughly 15x cheaper than the ``gpt-6-astra`` it replaces
  (model_ratio 1.0 vs 37.5), so the same ledger buys far more work. The quote is
  still built from the live response rather than from that observation.

Usage (from the server):
    HDP_RUN_HOURS=12 python /srv/lean/hdp-server-run.py
"""

from __future__ import annotations

import hashlib
import json
import os
import runpy
import subprocess
import urllib.error
import urllib.request
from datetime import UTC, datetime, timedelta
from pathlib import Path

ROOT = Path("/srv/lean")
PROJECT = ROOT / "fate-x-work"
BUDGETS = PROJECT / ".leanflow"
SOURCE_LEDGER = BUDGETS / "long-20261006-268m-budget.json"
NEW_LEDGER = BUDGETS / "long-20261008-200m-budget.json"
BASE_URL = "http://relay.example:3000/v1"
PRICING_URL = "http://relay.example:3000/api/pricing"
MODEL = "gpt-6-sol"
# The relay's own default group. Its cheaper alternatives (zcloud_grok_text_0.4x,
# zcloud_cc_kiro_0.4x) do not list gpt-6-sol among their enabled models, so the
# quote must name a group the model is actually routed through or the pricing
# would be fiction.
GROUP = "default"
# Hours are fixed at launch time and the deadline is derived, never extended
# implicitly: a relaunch recomputes from its own start rather than inheriting an
# earlier run's remaining time.
HOURS = float(str(os.getenv("HDP_RUN_HOURS", "") or "").strip() or "12")
DEADLINE_UTC = datetime.now(UTC) + timedelta(hours=HOURS)

os.environ["LEANFLOW_HOME"] = str(ROOT / ".leanflow-home")
os.environ["HDP_WORKSPACE"] = str(ROOT)
os.environ["HDP_LOCAL_LEAN_HOST"] = "1"
os.environ["LEANFLOW_LOCAL_PROJECT_ROOT"] = str(PROJECT)
os.environ["LEANFLOW_SCRATCH_ROOT"] = str(ROOT / "tmp")
os.environ.setdefault("TMPDIR", str(ROOT / "tmp"))
# The relay has no TLS listener, so the quote path refuses it by default. This is
# that explicit opt-in; see ALLOW_INSECURE_QUOTA_ENDPOINT_ENV in provider_quota.py.
os.environ["LEANFLOW_ALLOW_INSECURE_QUOTA_ENDPOINT"] = "1"
# hdp-scale pins the quote to this pair, so state it here rather than relying on
# its module defaults staying in step with this file.
os.environ["HDP_PROVIDER_BASE_URL"] = BASE_URL
os.environ["HDP_PROVIDER_MODEL"] = MODEL

scale = runpy.run_path(str(ROOT / "hdp-scale"))
from agent.accounting.provider_quota_budget import read_quota_budget
from leanflow_cli.config import load_env_file

STAMP = datetime.now(UTC).strftime("%Y%m%dT%H%M%SZ")
LOG = ROOT / ".leanflow-home/logs" / f"hdp-long-{STAMP}"
LOG.mkdir(parents=True, exist_ok=True)


# --- live keys ---------------------------------------------------------------
def _key_is_live(key: str) -> bool:
    """Return whether the relay accepts this credential; never spends quota."""
    req = urllib.request.Request(
        f"{BASE_URL}/models", headers={"Authorization": f"Bearer {key}"}
    )
    try:
        with urllib.request.urlopen(req, timeout=20) as r:
            return 200 <= int(r.status) < 300
    except urllib.error.HTTPError:
        return False
    except Exception:
        return False


vals = load_env_file()
raw_pool: list[str] = []
for src in (vals, os.environ):
    raw = str(src.get("M2F_CODEX_API_KEYS", "") or "").strip()
    if raw:
        raw_pool = [k.strip() for k in raw.split(",") if k.strip()]
        break
if not raw_pool:
    raise RuntimeError("M2F_CODEX_API_KEYS not found")
live_pool = [k for k in raw_pool if _key_is_live(k)]
print(f"keys: {len(raw_pool)} configured, {len(live_pool)} authenticate", flush=True)
# The operator's standing rule is that one working key is enough to keep running
# ("只要有 key 有效就可以一直跑"), so a short pool is not a reason to refuse. Only
# an empty pool is. hdp-scale binds worker slots to the live pool by modulo, so
# every slot still maps to a usable credential even when slots > keys.
if not live_pool:
    raise RuntimeError(f"no live key out of {len(raw_pool)} configured")

# --- really fetch the quote --------------------------------------------------
req = urllib.request.Request(
    PRICING_URL, headers={"Authorization": f"Bearer {live_pool[0]}"}
)
with urllib.request.urlopen(req, timeout=30) as r:
    pricing = json.loads(r.read().decode())
if not pricing.get("success"):
    raise RuntimeError("pricing fetch failed")
(LOG / "pricing.json").write_text(json.dumps(pricing, indent=2, ensure_ascii=False))
row = next(x for x in pricing["data"] if x["model_name"] == MODEL)
print(f"pricing_version {pricing['pricing_version'][:20]}", flush=True)
print(
    f"  {MODEL}: model_ratio {row['model_ratio']} completion_ratio "
    f"{row['completion_ratio']} group_ratio {pricing['group_ratio'][GROUP]}",
    flush=True,
)

template = json.loads((ROOT / ".leanflow-home/logs/quota-quote.json").read_text())
template.update(
    {
        "base_url": BASE_URL,
        "model": MODEL,
        "group": GROUP,
        "model_ratio": str(row["model_ratio"]),
        "completion_ratio": str(row["completion_ratio"]),
        "cache_read_ratio": str(row.get("cache_ratio", template.get("cache_read_ratio"))),
        "create_cache_ratio": str(
            row.get("create_cache_ratio", template["create_cache_ratio"])
        ),
        "group_ratio": str(pricing["group_ratio"][GROUP]),
        "group_ratio_bound": pricing["group_ratio"][GROUP],
        "pricing_version": pricing["pricing_version"],
        "evidence_path": str(LOG / "pricing.json"),
        "observed_at_utc": datetime.fromtimestamp(
            (LOG / "pricing.json").stat().st_mtime, UTC
        ).isoformat(),
        "group_ratio_evidence": f"GET /api/pricing on {datetime.now(UTC).date().isoformat()}",
    }
)
QUOTE = LOG / "quota-quote.json"
QUOTE.write_text(json.dumps(template, indent=2, ensure_ascii=False))
_, quote_meta = scale["verified_quote_snapshot"](QUOTE)
print(f"quote verified {quote_meta['sha256'][:16]}", flush=True)

# --- guard the source ledger -------------------------------------------------
source_sha_before = hashlib.sha256(SOURCE_LEDGER.read_bytes()).hexdigest()
budget = read_quota_budget(NEW_LEDGER)
print(
    f"ledger {NEW_LEDGER.name}: limit {budget['limit_quota']:,} "
    f"remaining {budget['remaining_quota']:,} held {budget['held_quota']:,}",
    flush=True,
)
if hashlib.sha256(SOURCE_LEDGER.read_bytes()).hexdigest() != source_sha_before:
    raise RuntimeError("source ledger changed; refusing to continue")
print("source ledger unchanged (byte-identical)", flush=True)

# --- the project tree must build before any paid work ------------------------
# The 2026-10-09 run spent four hours and then aborted at its first statement
# integration, because three abandoned proof attempts from earlier runs had left
# the tree uncompilable; the integration check builds the whole tree, so it
# could not verify even the rolled-back root. The runner now restores such
# attempts itself, but a tree broken by anything else -- a hand edit, an older
# runner -- would fail the same way, late and expensively. Building here costs a
# few minutes against a cached tree and turns that into an immediate refusal.
print("building the project tree (lake build FateXWork) ...", flush=True)
build = subprocess.run(
    [str(ROOT / "leanflow/remote-bin/lake"), "build", "FateXWork"],
    cwd=PROJECT,
    env={**os.environ, "PATH": f"/home/lean/.elan/bin:{os.environ.get('PATH', '')}"},
    capture_output=True,
    text=True,
    timeout=3600,
    check=False,
)
(LOG / "preflight-build.log").write_text(build.stdout + build.stderr, encoding="utf-8")
if build.returncode != 0:
    raise RuntimeError(
        f"project tree does not build (exit {build.returncode}); refusing to spend "
        f"quota on a run whose integration checks cannot pass. See {LOG / 'preflight-build.log'}"
    )
print("project tree builds", flush=True)

# --- the proof lane's verifier must exist ------------------------------------
# lean_incremental_check runs on the project's REPL executable, which `lake build
# FateXWork` does not build: it is a separate package target. The server had the
# repl *source* but never the binary, so from the migration until 2026-10-10
# every proof worker's check came back `local_repl_missing` (e.g. 46 of 55 in
# one attempt). The prover could edit but never confirm a proof, so
# proofs_completed stayed at 84 while statements -- which compile through lake
# directly -- kept advancing. That fails silently, so refuse to launch instead.
REPL_BINARY = PROJECT / ".lake/packages/repl/.lake/build/bin/repl"
if not REPL_BINARY.is_file():
    raise RuntimeError(
        f"proof verifier missing: {REPL_BINARY} does not exist. Build it with "
        f"`cd {PROJECT}/.lake/packages/repl && lake build repl` before launching."
    )
print(f"proof verifier present ({REPL_BINARY.name})", flush=True)

# --- launch ------------------------------------------------------------------
print(
    f"\nlaunching: {HOURS}h, 4 workers, model {MODEL} on {BASE_URL}",
    flush=True,
)

env = dict(os.environ)
env.update(
    {
        "M2F_CODEX_API_KEYS": ",".join(live_pool),
        "M2F_CODEX_API_KEY": live_pool[0],
        "PYTHONUNBUFFERED": "1",
        "PYTHONPATH": str(ROOT / "leanflow"),
        "PATH": f"/srv/lean/bin:/home/lean/.elan/bin:{ROOT}/leanflow/.venv/bin:"
        + env.get("PATH", ""),
        "HDP_SCALE_NO_INFRASTRUCTURE_FUSE": "0",
        "LEANFLOW_PROVIDER_QUOTA_IGNORE_UNKNOWN_HOLDS": "0",
        "LEANFLOW_ALLOW_INSECURE_QUOTA_ENDPOINT": "1",
        "LEANFLOW_API_TIMEOUT": "900",
        "LEANFLOW_REVIEWER_TIMEOUT_SECONDS": "900",
        "LEANFLOW_CAMPAIGN_CHILD_TIMEOUT_S": "14400",
        "LEANFLOW_MANAGER_LLM_MODE": "off",
    }
)

command = [
    str(ROOT / "leanflow/.venv/bin/python"),
    str(ROOT / "hdp-long-run"),
    "--continuous",
    "--no-extension",
    "--hours",
    str(round(HOURS - 0.05, 2)),
    "--workers",
    "4",
    "--budget",
    str(NEW_LEDGER),
    "--quote",
    str(QUOTE),
    "--log-dir",
    str(LOG),
]
with (LOG / "controller.log").open("x", encoding="utf-8") as handle:
    child = subprocess.Popen(
        command,
        cwd=ROOT,
        env=env,
        stdin=subprocess.DEVNULL,
        stdout=handle,
        stderr=subprocess.STDOUT,
        start_new_session=True,
    )
print(f"\ncontroller pid={child.pid}\nlog={LOG}/controller.log", flush=True)
print(
    f"deadline {DEADLINE_UTC.isoformat()} ({HOURS}h from now)\n"
    f"stop early: touch {LOG / 'STOP'}",
    flush=True,
)
