import Mathlib

open MeasureTheory

namespace ProbabilityTheory

/-- The cumulative distribution function of a measurable real-valued random variable
under a probability measure. -/
def cumulativeDistributionFunction
    (Ω : Type*) [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : Measurable X) : ℝ → ℝ :=
  fun t : ℝ => μ.real {ω : Ω | X ω ≤ t}

theorem cumulativeDistributionFunction_apply
    (Ω : Type*) [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : Measurable X) :
    ∀ t : ℝ,
      cumulativeDistributionFunction Ω μ X hX t =
        μ.real {ω : Ω | X ω ≤ t} := by
  set_option maxHeartbeats 5000 in
    first | (rfl; done) | (assumption; done) | (simp; done) | (norm_num; done) | (omega; done) | (linarith; done) | (ring; done) | (simp_all [cumulativeDistributionFunction]; done)

end ProbabilityTheory
