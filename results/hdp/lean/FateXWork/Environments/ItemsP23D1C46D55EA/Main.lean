import Mathlib

namespace RandomVariableDistribution

noncomputable def distribution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
    (X : Ω → ℝ) (_hX : Measurable X) : MeasureTheory.Measure ℝ :=
  MeasureTheory.Measure.map X P

 theorem distribution_event_probability
    {Ω : Type*} [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
    (X : Ω → ℝ) (hX : Measurable X)
    (B : Set ℝ) (hB : MeasurableSet B) :
    (distribution P X hX B : ENNReal) =
      (P {ω : Ω | X ω ∈ B} : ENNReal) := by
  rw [distribution]
  exact MeasureTheory.Measure.map_apply hX hB

end RandomVariableDistribution
