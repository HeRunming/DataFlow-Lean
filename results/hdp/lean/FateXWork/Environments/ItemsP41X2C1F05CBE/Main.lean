import Mathlib

open MeasureTheory
open ProbabilityTheory

/-- The error is at most `3 * sigma / sqrt N` with probability at least `99%`. -/
theorem error_at_most_three_sigma_over_sqrt_N_with_probability_99
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (error : Ω → ℝ) (sigma : ℝ) (N : ℕ)
    (h_measurable : Measurable error)
    (hN : 0 < N) :
    μ {ω : Ω | error ω ≤ 3 * sigma / Real.sqrt (N : ℝ)} ≥
      (99 : ENNReal) / 100 := by
  sorry
