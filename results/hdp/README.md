# High-Dimensional Probability: formalization results

Lean 4 formalizations of statements from Roman Vershynin, *High-Dimensional
Probability* (2nd edition), produced by the LeanFlow campaign in
[`../../leanflow/`](../../leanflow/). Snapshot taken 2026-10-12.

## What is here

| Path | Contents |
|---|---|
| [`lean/`](lean/) | A standalone Lake project: every module reachable from `FateXWork.lean` |
| [`PROVED.md`](PROVED.md) | The 85 campaign items whose proofs are complete, with their theorems |
| [`inventory.json`](inventory.json) | Every module in the snapshot: campaign batch, status, remaining `sorry` count |
| [`summary.json`](summary.json) | Campaign-wide counts |
| [`axiom-audit.txt`](axiom-audit.txt) | Raw `#print axioms` output for every theorem in the proved items |

## Status

The campaign has 1035 batches. At snapshot time:

| Campaign status | Batches |
|---|---|
| Proof completed | 85 |
| Statement accepted, proof open | 372 |
| Statement being retried | 355 |
| Proof being retried | 32 |
| Pending | 95 |
| Skipped (out of scope, e.g. prose or exercises without a formal claim) | 91 |
| Blocked on an unresolved dependency | 5 |

The snapshot contains 394 modules, the import closure of the project root:
228 contain no `sorry`, and 166 are accepted statements whose proofs are still
`sorry`. Of the 228, 119 hold only shared definitions and contain no theorem.
A statement-with-`sorry` is a faithful, reviewed, compiling *statement*, not a
proof; treat it as such.

## Verification

Both checks below were run on this exact snapshot, outside the campaign
workspace, against Lean 4.28.0 and Mathlib v4.28.0 with no other dependency.

- **Build.** `lake build` completes successfully (8420 jobs).
- **Axioms.** Every theorem in the 85 proved items (111 theorems) was checked
  with `#print axioms`. 110 depend only on `propext`, `Classical.choice` and
  `Quot.sound`; 1 depends on no axioms. None depends on `sorryAx` or on any
  non-standard axiom.
- **Escape hatches.** No file in the snapshot declares an `axiom` or uses
  `admit`, `sorryAx` or `unsafe`. Five *skipped* items (3.5, 9.6.4, p88.f1,
  p89.f1, p206.x1) contain `opaque` placeholders for notions the statement lane
  could not express. They carry no proofs and are not counted as results; the
  statement lane now rejects `opaque`. None of the 85 proved items uses it.

## Building

```bash
cd results/hdp/lean
lake exe cache get   # fetch prebuilt Mathlib
lake build
```

## Not included

The campaign's run state (`campaign.json`, per-attempt diagnostics, provider
billing receipts and compile receipts) and the model trajectories are not
published. They contain unfiltered model output and have not yet been cleaned.

Module names keep the campaign's layout (`FateXWork.Environments.Items…`);
`inventory.json` maps each to its book item.
