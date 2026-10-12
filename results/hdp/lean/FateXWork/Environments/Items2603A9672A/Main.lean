import Mathlib

open MeasureTheory
open ProbabilityTheory

private lemma gaussian_event_transfer
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (g : Ω → ℝ) (hg : Measurable g) (t : ℝ) :
    μ.real {ω : Ω | t ≤ g ω} = (Measure.map g μ).real (Set.Ici t) := by
  rw [Measure.real_def, Measure.real_def, Measure.map_apply hg measurableSet_Ici]
  rfl

/-- The standard Gaussian satisfies the exponential tail bound. -/
theorem standard_gaussian_tail_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (g : Ω → ℝ)
    (hg : Measurable g)
    (h_dist : Measure.map g μ = ProbabilityTheory.gaussianReal (0 : ℝ) (1 : NNReal)) :
    ∀ (t : ℝ), 0 ≤ t →
      μ.real {ω : Ω | t ≤ g ω} ≤ Real.exp (-(t ^ 2) / (2 : ℝ)) := by
  sorry
