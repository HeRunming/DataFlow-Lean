import Mathlib

open MeasureTheory

namespace ConcentrationBounds

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Markov's inequality for a nonnegative random variable on a probability space. -/
theorem markov_tail_bound (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : AEStronglyMeasurable X μ)
    (hX_integrable : Integrable X μ)
    (hX_nonneg : ∀ᵐ ω ∂μ, (0 : ℝ) ≤ X ω) (t : ℝ) (ht : 0 < t) :
    ENNReal.toReal (μ {ω : Ω | t ≤ X ω}) ≤
      ((∫ ω : Ω, X ω ∂μ : ℝ) / t) := by
  sorry

/-- Chebyshev's inequality for deviations from the mean. -/
theorem chebyshev_tail_bound (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : MemLp X 2 μ) (t : ℝ) (ht : 0 < t) :
    ENNReal.toReal (μ {ω : Ω | t ≤ |X ω - (∫ x : Ω, X x ∂μ : ℝ)|}) ≤
      ((∫ ω : Ω, (X ω - (∫ x : Ω, X x ∂μ : ℝ)) ^ 2 ∂μ : ℝ) / t ^ 2) := by
  sorry

end ConcentrationBounds
