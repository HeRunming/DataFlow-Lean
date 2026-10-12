import Mathlib

open MeasureTheory

universe u

/-- The source-defined conditional probability of one event given another. -/
noncomputable def eventConditionalProbability {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) (E F : Set Ω) : ENNReal :=
  μ (E ∩ F) / μ F

/-- The defining formula on the domain of ordinary event conditioning. -/
theorem conditional_probability_event_formula
    {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (E F : Set Ω)
    (hE : MeasurableSet E) (hF : MeasurableSet F)
    (hF_pos : (0 : ENNReal) < μ F) :
    eventConditionalProbability μ E F = μ (E ∩ F) / μ F := by
  set_option maxHeartbeats 5000 in
    first | (rfl; done) | (assumption; done) | (simp; done) | (norm_num; done) | (omega; done) | (linarith; done) | (ring; done)
