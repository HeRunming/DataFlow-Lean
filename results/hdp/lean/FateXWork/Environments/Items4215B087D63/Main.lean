import Mathlib

/--
Source: Definition 4.2.1 in `HDP/source/environments.json`.

Source proof: This is a definition; no proof is given in the source.
Proof sketch: An ε-net is a subset of `K` whose closed ε-balls cover every point of `K`.
Prover notes: The positive-radius hypothesis from the source is represented by the subtype
`{r : ℝ // 0 < r}`. The pointwise condition uses Mathlib's metric distance.
-/
def IsEpsilonNet {T : Type*} [MetricSpace T] (K N : Set T)
    (ε : {r : ℝ // 0 < r}) : Prop :=
  N ⊆ K ∧ ∀ x ∈ K, ∃ x₀ ∈ N, dist x x₀ ≤ ε

/--
Source: the ball-cover equivalence in Definition 4.2.1 of
`HDP/source/environments.json`.

Source proof: The equivalence follows by unfolding membership in a closed metric ball
and exchanging the pointwise and union formulations.
Proof sketch: `x ∈ closedBall x₀ ε` is definitionally the inequality
`dist x x₀ ≤ ε`; rewrite set inclusion into pointwise membership and unpack the union.
Prover notes: Closed balls are used because the source's displayed inequality is non-strict.
-/
theorem isEpsilonNet_iff_closedBallCover {T : Type*} [MetricSpace T]
    (K N : Set T) (ε : {r : ℝ // 0 < r}) :
    IsEpsilonNet K N ε ↔ N ⊆ K ∧ K ⊆ ⋃ x₀ ∈ N, Metric.closedBall x₀ (ε : ℝ) := by
  sorry
