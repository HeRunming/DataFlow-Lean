import Mathlib

/--
Source proof: The source is an explanatory remark and supplies no formal proof.
Proof sketch: represent the displayed tail profile directly and use positivity of `Real.exp`.
Prover notes: this is intentionally a partial formalization of the prose remark; the
probabilistic Hoeffding hypotheses and comparison with (2.3) are recorded in the blueprint.
-/
theorem remark_2_2_2_exponentially_light_tails (t : ℝ) :
    0 < Real.exp (-t ^ 2 / 2) := by
  sorry
