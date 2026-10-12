import Mathlib

open MeasureTheory
open ProbabilityTheory

theorem standard_score_reduction
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (X : Ω → ℝ)
    (hX_meas : AEStronglyMeasurable X P)
    (hX_memLp : MemLp X 2 P)
    (hvar_pos : variance X P > 0) :
    let m : ℝ := ∫ ω, X ω ∂P
    let Z : Ω → ℝ := fun ω => (X ω - m) / Real.sqrt (variance X P)
    AEStronglyMeasurable Z P ∧
      (∫ ω, Z ω ∂P) = 0 ∧
      variance Z P = 1 ∧
      (∀ ω : Ω, Z ω = (X ω - m) / Real.sqrt (variance X P)) ∧
      (∀ ω : Ω, X ω = m + Real.sqrt (variance X P) * Z ω) := by
  dsimp
  let m : ℝ := ∫ ω, X ω ∂P
  let s : ℝ := Real.sqrt (variance X P)
  have hs : 0 < s := Real.sqrt_pos.2 hvar_pos
  have hs0 : s ≠ 0 := ne_of_gt hs
  have hs2 : s ^ 2 = variance X P := by
    dsimp [s]
    exact Real.sq_sqrt (le_of_lt hvar_pos)
  have hXi : Integrable X P := hX_memLp.integrable one_le_two
  have hsub : variance (fun ω => X ω - m) P = variance X P :=
    variance_sub_const hX_meas m
  have hmeas : AEStronglyMeasurable (fun ω => (X ω - m) / s) P := by
    have hd : AEStronglyMeasurable (fun ω => X ω - m) P :=
      hX_meas.sub measurable_const.aestronglyMeasurable
    convert hd.const_mul s⁻¹ using 1
    · funext ω
      simp [div_eq_mul_inv, mul_comm]
  have hmean : (∫ ω, (X ω - m) / s ∂P) = 0 := by
    rw [show (fun ω => (X ω - m) / s) = fun ω => s⁻¹ * (X ω - m) by
      funext ω; simp [div_eq_mul_inv, mul_comm]]
    rw [integral_const_mul, integral_sub hXi (integrable_const m)]
    simp [m]
  have hvariance : variance (fun ω => (X ω - m) / s) P = 1 := by
    rw [show (fun ω => (X ω - m) / s) = fun ω => s⁻¹ * (X ω - m) by
      funext ω; simp [div_eq_mul_inv, mul_comm]]
    rw [variance_const_mul, hsub]
    have hs2' : s * s = variance X P := by nlinarith [hs2]
    field_simp [hs0, hs2']
    exact hs2.symm
  refine ⟨hmeas, hmean, hvariance, ?_, ?_⟩
  · intro ω
    rfl
  · intro ω
    change X ω = m + s * ((X ω - m) / s)
    field_simp [hs0]
    ring
