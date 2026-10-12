import Mathlib

open MeasureTheory

universe u

theorem markov_inequality_nonnegative
    {Ω : Type u} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX_measurable : Measurable X)
    (hX_nonnegative : ∀ ω : Ω, (0 : ℝ) ≤ X ω)
    (t : ℝ) (ht : (0 : ℝ) < t) :
    μ {ω : Ω | t ≤ X ω} ≤
      (∫⁻ ω : Ω, ENNReal.ofReal (X ω) ∂μ) / ENNReal.ofReal t := by
  have h := MeasureTheory.meas_ge_le_lintegral_div
    (μ := μ) (f := fun ω => ENNReal.ofReal (X ω))
    (hX_measurable.ennreal_ofReal.aemeasurable) (ENNReal.ofReal_pos.mpr ht).ne'
    ENNReal.ofReal_ne_top
  simpa only [ENNReal.ofReal_le_ofReal_iff, hX_nonnegative, Set.setOf_mem_eq] using h
