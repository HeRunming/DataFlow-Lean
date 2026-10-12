import Mathlib

open MeasureTheory

namespace ProbabilityTheory

 theorem mgf_le_two_point_distribution
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X Y : Ω → ℝ)
    (a b : ℝ)
    (hX_measurable : Measurable X)
    (hY_measurable : Measurable Y)
    (hX_range : ∀ ω : Ω, X ω ∈ Set.Icc a b)
    (hY_range : ∀ ω : Ω, Y ω = a ∨ Y ω = b)
    (hX_integrable : Integrable X μ)
    (hY_integrable : Integrable Y μ)
    (h_same_mean : (∫ ω : Ω, X ω ∂μ) = (∫ ω : Ω, Y ω ∂μ))
    (h_exp_integrable : ∀ coeff : ℝ,
      Integrable (fun ω : Ω => Real.exp (coeff * X ω)) μ ∧
      Integrable (fun ω : Ω => Real.exp (coeff * Y ω)) μ) :
    ∀ coeff : ℝ,
      (∫ ω : Ω, Real.exp (coeff * X ω) ∂μ) ≤
        (∫ ω : Ω, Real.exp (coeff * Y ω) ∂μ) := by
  classical
  intro coeff
  by_cases hΩ : Nonempty Ω
  · obtain ⟨ω₀⟩ := hΩ
    have hab : a ≤ b := (hX_range ω₀).1.trans (hX_range ω₀).2
    by_cases heq : a = b
    · subst b
      have hx : ∀ ω, X ω = a := fun ω => le_antisymm (hX_range ω).2 (hX_range ω).1
      have hy : ∀ ω, Y ω = a := fun ω => (hY_range ω).elim id id
      simp only [hx, hy, le_refl]
    · have hd : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm heq)
      have hp : 0 < b - a := sub_pos.mpr (lt_of_le_of_ne hab heq)
      have chord : ∀ ω, Real.exp (coeff * X ω) ≤
          (b - X ω) / (b-a) * Real.exp (coeff*a) +
          (X ω-a) / (b-a) * Real.exp (coeff*b) := by
        intro ω
        have hu : 0 ≤ (b-X ω)/(b-a) := div_nonneg (sub_nonneg.mpr (hX_range ω).2) hp.le
        have hv : 0 ≤ (X ω-a)/(b-a) := div_nonneg (sub_nonneg.mpr (hX_range ω).1) hp.le
        have hs : (b-X ω)/(b-a) + (X ω-a)/(b-a) = 1 := by field_simp; ring
        have ht : (b-X ω)/(b-a) * (coeff*a) + (X ω-a)/(b-a) * (coeff*b) = coeff * X ω := by field_simp; ring
        have hc := convexOn_exp.2 (Set.mem_univ (coeff*a)) (Set.mem_univ (coeff*b)) hu hv hs
        simpa only [smul_eq_mul, ht] using hc
      have affine : ∀ (Z : Ω → ℝ), Integrable Z μ →
          (∫ ω, (b-Z ω)/(b-a)*Real.exp (coeff*a) + (Z ω-a)/(b-a)*Real.exp (coeff*b) ∂μ) =
          (b-(∫ ω, Z ω ∂μ))/(b-a)*Real.exp (coeff*a) + ((∫ ω, Z ω ∂μ)-a)/(b-a)*Real.exp (coeff*b) := by
        intro Z hZ
        have hl := ((integrable_const b).sub hZ).div_const (b-a)
        have hr := (hZ.sub (integrable_const a)).div_const (b-a)
        calc
          (∫ ω, (b-Z ω)/(b-a)*Real.exp (coeff*a) + (Z ω-a)/(b-a)*Real.exp (coeff*b) ∂μ) =
              (∫ ω, (b-Z ω)/(b-a)*Real.exp (coeff*a) ∂μ) +
                (∫ ω, (Z ω-a)/(b-a)*Real.exp (coeff*b) ∂μ) :=
            integral_add (hl.mul_const _) (hr.mul_const _)
          _ = (b-(∫ ω, Z ω ∂μ))/(b-a)*Real.exp (coeff*a) +
                ((∫ ω, Z ω ∂μ)-a)/(b-a)*Real.exp (coeff*b) := by
            simp only [integral_mul_const, integral_div, integral_sub (integrable_const b) hZ,
              integral_sub hZ (integrable_const a), integral_const, probReal_univ, one_smul]
      have hR : Integrable (fun ω => (b-X ω)/(b-a)*Real.exp (coeff*a) + (X ω-a)/(b-a)*Real.exp (coeff*b)) μ :=
        ((((integrable_const b).sub hX_integrable).div_const (b-a)).mul_const _).add
          (((hX_integrable.sub (integrable_const a)).div_const (b-a)).mul_const _)
      have hy : ∀ ω, (b-Y ω)/(b-a)*Real.exp (coeff*a) + (Y ω-a)/(b-a)*Real.exp (coeff*b) = Real.exp (coeff*Y ω) := by
        intro ω
        rcases hY_range ω with h | h <;> simp [h, hd]
      calc
        _ ≤ ∫ ω, (b-X ω)/(b-a)*Real.exp (coeff*a) + (X ω-a)/(b-a)*Real.exp (coeff*b) ∂μ :=
          integral_mono_ae (h_exp_integrable coeff).1 hR (ae_of_all _ chord)
        _ = ∫ ω, (b-Y ω)/(b-a)*Real.exp (coeff*a) + (Y ω-a)/(b-a)*Real.exp (coeff*b) ∂μ := by
          rw [affine X hX_integrable, affine Y hY_integrable, h_same_mean]
        _ = _ := integral_congr_ae (ae_of_all _ hy)
  · haveI : IsEmpty Ω := not_nonempty_iff.mp hΩ
    have hXY : X = Y := funext fun ω => isEmptyElim ω
    rw [hXY]

end ProbabilityTheory
