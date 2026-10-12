import Mathlib

open MeasureTheory ProbabilityTheory

noncomputable section

namespace Source

/-- A source-faithful formulation of a real-valued normal distribution via its MGF. -/
def HasNormalDistribution
    {Ω : Type*} [MeasurableSpace Ω] (X : Ω → ℝ) (P : Measure Ω)
    (μ variance : ℝ) : Prop :=
  Measurable X ∧
    ∀ t : ℝ,
      Integrable (fun ω : Ω => Real.exp (t * X ω)) P ∧
        ∫ ω : Ω, Real.exp (t * X ω) ∂P =
          Real.exp (μ * t + variance * t ^ 2 / (2 : ℝ))

theorem sum_independent_normal
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {n : ℕ} (hn : 0 < n)
    (X : Fin n → Ω → ℝ)
    (μi σ : Fin n → ℝ)
    (h_indep : iIndepFun X P)
    (h_normal : ∀ i : Fin n,
      HasNormalDistribution (X i) P (μi i) ((σ i) ^ 2)) :
    HasNormalDistribution
      (fun ω : Ω => ∑ i : Fin n, X i ω)
      P
      (∑ i : Fin n, μi i)
      (∑ i : Fin n, (σ i) ^ 2) := by
  classical
  unfold HasNormalDistribution at *
  have hmX : ∀ i : Fin n, Measurable (X i) := fun i => (h_normal i).1
  constructor
  · exact Finset.measurable_sum _ (fun i _ => hmX i)
  · intro t
    let f : Fin n → ℝ → ℝ := fun _ x => Real.exp (t * x)
    have hf : ∀ i, AEStronglyMeasurable (f i) (P.map (X i)) := by
      intro i
      exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).aestronglyMeasurable
    have hfm : ∀ i, Measurable (f i) := by
      intro i
      exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).measurable
    have hfm_comp : ∀ i, Measurable (f i ∘ X i) := fun i => (hfm i).comp (hmX i)
    have h_indep_f : iIndepFun (fun i => f i ∘ X i) P := h_indep.comp f hfm
    have hi : ∀ i, Integrable (f i ∘ X i) P := by
      intro i
      simpa [f, Function.comp_def] using (h_normal i).2 t |>.1
    have hprodInt' : Integrable (∏ i : Fin n, f i ∘ X i) P := by
      induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
      | empty => exact (integrable_const (c := (1 : ℝ)) : Integrable (fun _ : Ω => (1 : ℝ)) P)
      | @insert a s ha ih =>
          have hpair := h_indep_f.indepFun_finset_prod_of_notMem (fun i => hfm_comp i) ha
          have hmul := hpair.integrable_mul ih (hi a)
          simpa [Finset.prod_insert, ha, mul_comm] using hmul
    have hprodInt : Integrable (fun ω => ∏ i : Fin n, f i (X i ω)) P := by
      convert hprodInt' using 1
      ext ω
      simp [Function.comp_def]
    have hprod := h_indep.integral_fun_prod_comp (fun i => (hmX i).aemeasurable) hf
    have hpoint : (fun ω => Real.exp (t * ∑ i : Fin n, X i ω)) = (fun ω => ∏ i : Fin n, f i (X i ω)) := by
      funext ω
      rw [show t * ∑ i : Fin n, X i ω = ∑ i : Fin n, t * X i ω by rw [Finset.mul_sum]]
      simp only [f]
      rw [← Real.exp_sum]
    constructor
    · rw [hpoint]
      exact hprodInt
    · rw [hpoint, hprod]
      simp only [f]
      calc
        (∏ i : Fin n, ∫ ω : Ω, Real.exp (t * X i ω) ∂P) = ∏ i : Fin n, Real.exp (μi i * t + (σ i) ^ 2 * t ^ 2 / 2) := by
          apply Finset.prod_congr rfl
          intro i hi'
          exact (h_normal i).2 t |>.2
        _ = Real.exp (∑ i : Fin n, (μi i * t + (σ i) ^ 2 * t ^ 2 / 2)) := by rw [← Real.exp_sum]
        _ = Real.exp ((∑ i : Fin n, μi i) * t + (∑ i : Fin n, (σ i) ^ 2) * t ^ 2 / 2) := by
          congr 1
          rw [Finset.sum_add_distrib]
          have hμ : (∑ i : Fin n, μi i * t) = (∑ i : Fin n, μi i) * t := by rw [Finset.sum_mul]
          have hσ : (∑ i : Fin n, (σ i) ^ 2 * t ^ 2 / 2) = (∑ i : Fin n, (σ i) ^ 2) * t ^ 2 / 2 := by
            simp only [div_eq_mul_inv]
            rw [Finset.sum_mul, Finset.sum_mul]
          rw [hμ, hσ]

end Source
