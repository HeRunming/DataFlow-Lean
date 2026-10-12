# The HDP campaign harness

This directory is a snapshot of **LeanFlow**, the Lean-first automation kernel
that produced the High-Dimensional Probability formalizations in
[`../results/hdp/`](../results/hdp/). LeanFlow itself is documented in
[`README.md`](README.md) and [`ARCHITECTURE.md`](ARCHITECTURE.md); this note
covers only how the HDP campaign drives it.

It is vendored for provenance and reproducibility. It is independent of the
`dataflow_lean` package: it has its own dependencies and its own test suite, and
the repository's root `pytest` run does not collect it.

## Layout

| Path | Role |
|---|---|
| [`hdp/hdp-server-run.py`](hdp/hdp-server-run.py) | Launcher: probes keys, fetches a live provider quote, refuses to start unless the tree builds and the REPL exists, then starts the supervisor |
| [`hdp/hdp-long-run`](hdp/hdp-long-run) | Continuous supervisor: runs waves until the deadline, recovering between them |
| [`hdp/hdp-scale`](hdp/hdp-scale) | One wave: leases batches, runs workers in parallel, classifies each outcome, pauses or stops dispatch |
| [`hdp/hdp-run`](hdp/hdp-run) | Per-worker launcher: builds the child environment and runs one campaign action |
| [`hdp/hdp-sync.py`](hdp/hdp-sync.py) | Copies the launchers to the Lean host and repairs their interpreter paths |
| [`leanflow_cli/formalization/`](leanflow_cli/formalization/) | Statement lane, proof lane, integration into the project root, recovery |
| [`agent/accounting/`](agent/accounting/) | Provider-quota ledger: reservations, receipts, reconciliation |

## The pipeline

Each book item is one campaign batch and becomes one Lean module.

1. **Statement lane.** A model drafts a Lean statement whose proof is
   `by sorry`. Drafts are rejected for forbidden tokens (`axiom`, `opaque`,
   `admit`, …), linted against the source's quantifiers and domains, compiled,
   and judged by an independent reviewer. An accepted statement is wrapped in a
   namespace unique to its module, so independently generated files never
   collide when imported together.
2. **Integration.** Between waves, accepted statements are imported into the
   project root and the whole tree is rebuilt. A failed build is rolled back.
3. **Proof lane.** A prover agent works on root-reachable statements, checking
   each step with an incremental Lean REPL. A completed proof must compile with
   no `sorry`. A failed attempt that left its target uncompilable is restored to
   the pre-attempt source; one that still compiles keeps its progress.

## Configuration

Deployment specifics are placeholders in this snapshot: the Lean host is
`lean@lean-host.example`, the provider relay is `http://relay.example:3000/v1`,
paths are under `/opt/hdp` and `/srv/lean`, and credential fingerprints are
zeroed. Substitute your own:

| Setting | Where |
|---|---|
| Provider base URL and model | `HDP_PROVIDER_BASE_URL`, `HDP_PROVIDER_MODEL` |
| Workspace root | `HDP_WORKSPACE` |
| Run on the Lean host itself | `HDP_LOCAL_LEAN_HOST=1` |
| Allowed credentials | `AUTHORIZED_KEY_SHA256S` in `hdp/hdp-run` (SHA-256 of each key) |
| Lean host and paths | `hdp/hdp-run`, `remote-bin/lake`, `leanflow_cli/formalization/remote_warm_probe.py` |
| Plain-HTTP relay | `LEANFLOW_ALLOW_INSECURE_QUOTA_ENDPOINT=1`, an explicit opt-in |

Credentials are read only from the environment or the managed `.env`; they are
never written to logs, receipts or this repository.

## Tests

```bash
cd leanflow
python -m pip install -e .
python -m pytest -q
```

Four tests read a live deployment's logs and campaign state and are skipped
without one. Two tests in `tests/tools/` are known to fail on this snapshot
independent of the HDP work.
