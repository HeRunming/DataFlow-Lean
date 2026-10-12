import Mathlib

open MeasureTheory

namespace SubexponentialMGF

private theorem exp_one_map {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ)
    (hm : Measurable X)
    (h : ∀ x : ℝ, μ {ω | X ω ≤ x} = if 0 ≤ x then ENNReal.ofReal (1 - Real.exp (-x)) else 0) :
    Measure.map X μ = ProbabilityTheory.expMeasure 1 := by
  letI : IsProbabilityMeasure (ProbabilityTheory.expMeasure (1 : ℝ)) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure (by norm_num)
  apply Measure.ext_of_Iic
  intro x
  rw [Measure.map_apply hm measurableSet_Iic]
  change μ {ω | X ω ≤ x} = _
  rw [h]
  have hc := ProbabilityTheory.cdf_expMeasure_eq (by norm_num : (0 : ℝ) < 1) x
  rw [ProbabilityTheory.cdf_eq_real] at hc
  have he := congrArg ENNReal.ofReal hc
  simpa only [Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _), one_mul,
    apply_ite ENNReal.ofReal, ENNReal.ofReal_zero] using he.symm

private theorem exp_one_lintegral_map {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ)
    (hm : Measurable X)
    (h : ∀ x : ℝ, μ {ω | X ω ≤ x} = if 0 ≤ x then ENNReal.ofReal (1 - Real.exp (-x)) else 0)
    (f : ℝ → ENNReal)
    (hf : AEMeasurable f (ProbabilityTheory.expMeasure 1)) :
    (∫⁻ ω, f (X ω) ∂μ) = ∫⁻ x, f x ∂ProbabilityTheory.expMeasure 1 := by
  have hmap := exp_one_map μ X hm h
  have hf' : AEMeasurable f (Measure.map X μ) := by
    rw [hmap]
    exact hf
  rw [← MeasureTheory.lintegral_map' hf' hm.aemeasurable, hmap]

private theorem exp_diverges (c : ℝ) (hc : 1 ≤ c) :
    (∫⁻ x, ENNReal.ofReal (Real.exp (c*x)) ∂ProbabilityTheory.expMeasure 1) = ⊤ := by
  have hm : Measurable (ProbabilityTheory.gammaPDF 1 1) := by
    unfold ProbabilityTheory.gammaPDF ProbabilityTheory.gammaPDFReal
    apply Measurable.ennreal_ofReal
    apply Measurable.ite (measurableSet_le measurable_const measurable_id)
    · fun_prop
    · fun_prop
  unfold ProbabilityTheory.expMeasure ProbabilityTheory.gammaMeasure
  rw [lintegral_withDensity_eq_lintegral_mul₀ hm.aemeasurable (by fun_prop)]
  apply top_unique
  calc
    ⊤ = ∫⁻ x : ℝ, (Set.Ioi (0 : ℝ)).indicator (fun _ => (1 : ENNReal)) x := by simp
    _ ≤ _ := by
      apply lintegral_mono
      intro x
      by_cases hx : x ∈ Set.Ioi (0 : ℝ)
      · rw [Set.indicator_of_mem hx]
        change 0 < x at hx
        change 1 ≤ ProbabilityTheory.gammaPDF 1 1 x * ENNReal.ofReal (Real.exp (c*x))
        simp only [ProbabilityTheory.gammaPDF, ProbabilityTheory.gammaPDFReal,
          if_pos (le_of_lt hx), Real.rpow_one, Real.Gamma_one, div_one,
          sub_self, Real.rpow_zero, mul_one, one_mul]
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
        have he : 1 ≤ Real.exp (-x + c*x) := Real.one_le_exp_iff.mpr (by nlinarith)
        exact_mod_cast ENNReal.ofReal_le_ofReal he
      · rw [Set.indicator_of_notMem hx]
        exact zero_le _

theorem exp_one_mgf_infinite_at_or_above_one
    {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ)
    (hX_measurable : Measurable X)
    (hX_exp_one : ∀ x : ℝ,
      μ {ω : Ω | X ω ≤ x} =
        if 0 ≤ x then ENNReal.ofReal (1 - Real.exp (-x)) else 0) :
    ∀ coeff : ℝ, 1 ≤ coeff →
      ∫⁻ ω, ENNReal.ofReal (Real.exp (coeff * X ω)) ∂μ = ⊤ := by
  intro coeff hcoeff
  calc
    (∫⁻ ω, ENNReal.ofReal (Real.exp (coeff * X ω)) ∂μ) =
        ∫⁻ x, ENNReal.ofReal (Real.exp (coeff * x)) ∂ProbabilityTheory.expMeasure 1 := by
      exact exp_one_lintegral_map μ X hX_measurable hX_exp_one
        (fun x => ENNReal.ofReal (Real.exp (coeff * x))) (by fun_prop)
    _ = ⊤ := exp_diverges coeff hcoeff

end SubexponentialMGF
