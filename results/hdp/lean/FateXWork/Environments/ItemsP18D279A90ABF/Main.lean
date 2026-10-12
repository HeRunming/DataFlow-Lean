import Mathlib

open MeasureTheory
open ProbabilityTheory

theorem expectation_variance_identity
    {Ω : Type*}
    [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    (X : Ω → ℝ)
    (hX_measurable : Measurable X)
    (hX2 : MeasureTheory.MemLp X (2 : ENNReal) μ) :
    ProbabilityTheory.variance X μ =
      (∫ (ω : Ω),
        (X ω - (∫ (x : Ω), X x ∂μ : ℝ)) ^ (2 : Nat) ∂μ : ℝ) := by
  sorry
