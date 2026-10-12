import Mathlib

open MeasureTheory

universe u

/-- Cauchy–Schwarz inequality for real-valued square-integrable random variables. -/
theorem random_variables_cauchy_schwarz
    {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω)
    (X Y : Ω → ℝ)
    (hX_measurable : AEStronglyMeasurable X μ)
    (hY_measurable : AEStronglyMeasurable Y μ)
    (hX_L2 : MemLp X (2 : ENNReal) μ)
    (hY_L2 : MemLp Y (2 : ENNReal) μ) :
    (∫ ω : Ω, |X ω * Y ω| ∂μ) ≤
      Real.sqrt (∫ ω : Ω, (X ω) ^ (2 : ℕ) ∂μ) *
      Real.sqrt (∫ ω : Ω, (Y ω) ^ (2 : ℕ) ∂μ) := by
  simpa [abs_mul, Real.sqrt_eq_rpow, Real.rpow_two, sq_abs] using
    (integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) (p := 2) (q := 2)
      (by constructor <;> norm_num)
      (f := fun ω => |X ω|) (g := fun ω => |Y ω|)
      (by filter_upwards [] with ω using abs_nonneg (X ω))
      (by filter_upwards [] with ω using abs_nonneg (Y ω))
      (by simpa [Real.norm_eq_abs] using hX_L2.norm)
      (by simpa [Real.norm_eq_abs] using hY_L2.norm))
