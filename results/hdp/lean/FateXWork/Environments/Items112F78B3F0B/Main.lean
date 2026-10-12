import Mathlib

open MeasureTheory

 theorem lp_interpolation_random_variable
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX_measurable : Measurable X)
    (p : ℝ) (hp : (1 : ℝ) < p) :
    MeasureTheory.eLpNorm' X p μ ≤
      ENNReal.rpow (MeasureTheory.eLpNorm' X (1 : ℝ) μ) ((1 : ℝ) / p) *
        ENNReal.rpow (MeasureTheory.eLpNorm X (⊤ : ENNReal) μ)
          ((1 : ℝ) - (1 : ℝ) / p) := by
  sorry
