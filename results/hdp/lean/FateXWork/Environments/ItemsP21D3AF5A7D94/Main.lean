import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace

open MeasureTheory

namespace ConditionalProbability

variable {Ω β : Type*}
variable [MeasurableSpace Ω] [MeasurableSpace β]
variable (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- Conditional probability of an event given a random variable. -/
noncomputable def conditionalProbability
    (E : Set Ω) (Y : Ω → β) : Ω → ℝ :=
  MeasureTheory.condExp
    (MeasurableSpace.comap Y inferInstance)
    μ
    (E.indicator (fun _ : Ω => (1 : ℝ)))

/-- The conditional probability of an event given a random variable is the
conditional expectation of its indicator. -/
theorem conditionalProbability_eq_conditional_expectation
    (E : Set Ω)
    (Y : Ω → β)
    (hE : MeasurableSet E)
    (hY : Measurable Y) :
    conditionalProbability μ E Y =
      MeasureTheory.condExp
        (MeasurableSpace.comap Y inferInstance)
        μ
        (E.indicator (fun _ : Ω => (1 : ℝ))) := by
  set_option maxHeartbeats 5000 in
    first | (rfl; done) | (assumption; done) | (simp; done) | (norm_num; done) | (omega; done) | (linarith; done) | (ring; done)

end ConditionalProbability
