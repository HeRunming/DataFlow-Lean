import Mathlib

open MeasureTheory

theorem expectation_indicator_eq_probability
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (E : Set Ω) (hE : MeasurableSet E) :
    (∫ ω : Ω, E.indicator (fun _ : Ω => (1 : ℝ)) ω ∂μ) = (μ E).toReal := by sorry
