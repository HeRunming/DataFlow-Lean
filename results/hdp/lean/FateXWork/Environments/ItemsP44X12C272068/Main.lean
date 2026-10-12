import Mathlib.Probability.Distributions.Gaussian.Real

open MeasureTheory ProbabilityTheory

namespace StandardNormalSource

noncomputable def standardNormal : Measure ℝ :=
  ProbabilityTheory.gaussianReal (0 : ℝ) (1 : NNReal)

noncomputable def sourceLpNorm (p : ℝ) : ℝ :=
  (∫ x : ℝ, Real.rpow |x| p ∂standardNormal) ^ ((1 : ℝ) / p)

theorem standard_normal_mgf :
    ProbabilityTheory.mgf id standardNormal =
      (fun coeff : ℝ => Real.exp (coeff ^ 2 / (2 : ℝ))) := by
  change ProbabilityTheory.mgf id (ProbabilityTheory.gaussianReal (0 : ℝ) (1 : NNReal)) = _
  rw [ProbabilityTheory.mgf_id_gaussianReal]
  funext coeff
  norm_num

private lemma power_exp_bound (t p : ℝ) (ht : 0 ≤ t) (hp : 0 < p) :
    t ^ p ≤ p ^ p * Real.exp t := by
  rcases eq_or_lt_of_le ht with rfl | ht
  · simp [Real.zero_rpow (ne_of_gt hp), le_of_lt (Real.rpow_pos_of_pos hp p)]
  · have hlog := Real.log_le_sub_one_of_pos (div_pos ht hp)
    rw [Real.log_div (ne_of_gt ht) (ne_of_gt hp)] at hlog
    rw [Real.rpow_def_of_pos ht, Real.rpow_def_of_pos hp, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h := (mul_le_mul_of_nonneg_right hlog (le_of_lt hp))
    field_simp at h
    nlinarith

private lemma standard_normal_moment_nonneg (p : ℝ) :
    0 ≤ ∫ x : ℝ, |x| ^ p ∂standardNormal := by
  apply integral_nonneg
  intro x
  positivity

private lemma standard_normal_positive_exponent (p : ℝ) (hp : 1 ≤ p) : 0 < p := by
  linarith

private lemma gaussian_real_density_formula :
    ProbabilityTheory.gaussianReal (0 : ℝ) (1 : NNReal) =
      Measure.withDensity MeasureTheory.volume
        (fun x : ℝ => ProbabilityTheory.gaussianPDF (0 : ℝ) (1 : NNReal) x) := by
  simp [ProbabilityTheory.gaussianReal]

private lemma absolute_power_gaussian_domination (x p : ℝ) (hp : 0 < p) :
    |x| ^ p ≤ (2 * p) ^ (p / 2) * Real.exp (x ^ 2 / 4) := by
  have h := power_exp_bound (x ^ 2 / 4) (p / 2) (by positivity) (by linarith)
  have hid : |x| ^ p = (4 : ℝ) ^ (p / 2) * (x ^ 2 / 4) ^ (p / 2) := by
    rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) (by positivity)]
    have hb : (4 : ℝ) * (x ^ 2 / 4) = |x| ^ (2 : ℝ) := by
      rw [Real.rpow_two, sq_abs]
      ring
    rw [hb, ← Real.rpow_mul (abs_nonneg x)]
    congr 1
    ring
  rw [hid]
  calc
    _ ≤ (4 : ℝ) ^ (p / 2) * ((p / 2) ^ (p / 2) * Real.exp (x ^ 2 / 4)) := mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by
      rw [← mul_assoc, ← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) (by positivity)]
      congr 2
      ring

private lemma exp_square_integrable : Integrable (fun x : ℝ => Real.exp (x ^ 2 / 4)) standardNormal := by
  rw [show standardNormal = gaussianReal (0 : ℝ) (1 : NNReal) by rfl, gaussian_real_density_formula]
  apply (integrable_withDensity_iff (by fun_prop) (Filter.Eventually.of_forall (fun x => by simp [gaussianPDF]))).2
  have h := integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 4)
  have he : (fun x : ℝ => Real.exp (x ^ 2 / 4) * (gaussianPDF 0 1 x).toReal) =
      (fun x : ℝ => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(1 / 4 : ℝ) * x ^ 2)) := by
    funext x
    simp [gaussianPDF, gaussianPDFReal, Real.exp_pos, Real.exp_nonneg]
    rw [mul_left_comm, ← Real.exp_add]
    congr 2 <;> ring
  rw [he]
  exact h.const_mul _

private lemma standard_normal_moment_bound_by_exp (p : ℝ) (hp : 0 < p) :
    (∫ x : ℝ, |x| ^ p ∂standardNormal) ≤
      (2 * p) ^ (p / 2) * (|∫ x : ℝ, Real.exp (x ^ 2 / 4) ∂standardNormal| + 1) := by
  calc
    _ ≤ ∫ x : ℝ, (2 * p) ^ (p / 2) * Real.exp (x ^ 2 / 4) ∂standardNormal := by
      apply integral_mono_of_nonneg
      · exact Filter.Eventually.of_forall (fun x => Real.rpow_nonneg (abs_nonneg x) p)
      · exact exp_square_integrable.const_mul _
      · exact Filter.Eventually.of_forall (fun x => absolute_power_gaussian_domination x p hp)
    _ = (2 * p) ^ (p / 2) * ∫ x : ℝ, Real.exp (x ^ 2 / 4) ∂standardNormal := by rw [integral_const_mul]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith [le_abs_self (∫ x : ℝ, Real.exp (x ^ 2 / 4) ∂standardNormal)]

theorem standard_normal_absolute_moment_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ p : ℝ, 1 ≤ p →
      sourceLpNorm p ≤ C * Real.sqrt p := by
  let I : ℝ := ∫ x : ℝ, Real.exp (x ^ 2 / 4) ∂standardNormal
  let K : ℝ := |I| + 1
  have hK : 1 ≤ K := by dsimp [K]; linarith [abs_nonneg I]
  refine ⟨Real.sqrt 2 * K, mul_pos (by positivity) (by linarith), ?_⟩
  intro p hp
  have hp0 : 0 < p := by linarith
  have hb : (∫ x : ℝ, |x| ^ p ∂standardNormal) ≤ (2 * p) ^ (p / 2) * K :=
    standard_normal_moment_bound_by_exp p hp0
  have he : 1 / p ≤ (1 : ℝ) := (div_le_one hp0).2 hp
  have hkpow : K ^ (1 / p) ≤ K := by
    calc
      _ ≤ K ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hK he
      _ = K := Real.rpow_one K
  unfold sourceLpNorm
  calc
    _ ≤ ((2 * p) ^ (p / 2) * K) ^ (1 / p) := Real.rpow_le_rpow (standard_normal_moment_nonneg p) hb (by positivity)
    _ = Real.sqrt (2 * p) * K ^ (1 / p) := by
      rw [Real.mul_rpow (by positivity) (by linarith : 0 ≤ K), ← Real.rpow_mul (by positivity)]
      rw [show p / 2 * (1 / p) = (1 / 2 : ℝ) by field_simp]
      rw [← Real.sqrt_eq_rpow]
    _ ≤ Real.sqrt (2 * p) * K := mul_le_mul_of_nonneg_left hkpow (Real.sqrt_nonneg _)
    _ = Real.sqrt 2 * K * Real.sqrt p := by rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]; ring

end StandardNormalSource
