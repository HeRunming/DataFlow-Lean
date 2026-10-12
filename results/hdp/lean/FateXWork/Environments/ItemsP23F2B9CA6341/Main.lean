import Mathlib

/--
Source proof: The source refers to Exercise 1.11; its proof text is not included in the
supplied excerpt.
Proof sketch: apply `MeasureTheory.eLpNorm'_le_eLpNorm'_of_exponent_le` using positivity
of `p`, the hypothesis `p ≤ q`, the probability-measure instance, and a.e. strong
measurability of `f`.
Prover notes: this is the precise measure-theoretic form of the informal monotonicity
claim for `L^p` norms.
-/
theorem lp_norm_mono_probability {α ε : Type*} [MeasurableSpace α]
    [TopologicalSpace ε] [ContinuousENorm ε]
    {f : α → ε} {p q : ℝ} (hp : 0 < p) (hpq : p ≤ q)
    (μ : MeasureTheory.Measure α) [MeasureTheory.IsProbabilityMeasure μ]
    (hf : MeasureTheory.AEStronglyMeasurable f μ) :
    MeasureTheory.eLpNorm' f p μ ≤ MeasureTheory.eLpNorm' f q μ := by
  sorry
