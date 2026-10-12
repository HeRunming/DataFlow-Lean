import Mathlib

open MeasureTheory

theorem minkowski_inequality
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (p : ENNReal) (X Y : α → ℝ)
    (hp : (1 : ENNReal) ≤ p)
    (hX_measurable : Measurable X)
    (hY_measurable : Measurable Y)
    (hX_memLp : MemLp X p μ)
    (hY_memLp : MemLp Y p μ) :
    (eLpNorm (X + Y) p μ).toReal ≤
      (eLpNorm X p μ).toReal + (eLpNorm Y p μ).toReal := by
  have htriangle := eLpNorm_add_le (μ := μ) hX_measurable.aestronglyMeasurable
    hY_measurable.aestronglyMeasurable hp
  have hfinite := ENNReal.add_ne_top.mpr
    ⟨hX_memLp.eLpNorm_lt_top.ne, hY_memLp.eLpNorm_lt_top.ne⟩
  have hreal := ENNReal.toReal_mono hfinite htriangle
  rwa [ENNReal.toReal_add hX_memLp.eLpNorm_lt_top.ne hY_memLp.eLpNorm_lt_top.ne] at hreal
