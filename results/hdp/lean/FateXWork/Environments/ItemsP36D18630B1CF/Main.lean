import Mathlib

namespace Source

/-- The source-defined Rademacher predicate for a real random variable. -/
def HasRademacherDistribution
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) (X : Ω → ℝ) : Prop :=
  Measurable X ∧
    μ {ω : Ω | X ω = (-1 : ℝ)} = (1 : ENNReal) / (2 : ENNReal) ∧
    μ {ω : Ω | X ω = (1 : ℝ)} = (1 : ENNReal) / (2 : ENNReal)

/-- A random variable is Rademacher exactly when each sign has probability one half. -/
theorem hasRademacherDistribution_iff
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : Measurable X) :
    HasRademacherDistribution μ X ↔
      (μ {ω : Ω | X ω = (-1 : ℝ)} = (1 : ENNReal) / (2 : ENNReal) ∧
       μ {ω : Ω | X ω = (1 : ℝ)} = (1 : ENNReal) / (2 : ENNReal)) := by
  set_option maxHeartbeats 5000 in
    first | (rfl; done) | (assumption; done) | (simp; done) | (norm_num; done) | (omega; done) | (linarith; done) | (ring; done) | (simp_all [HasRademacherDistribution]; done)

end Source
