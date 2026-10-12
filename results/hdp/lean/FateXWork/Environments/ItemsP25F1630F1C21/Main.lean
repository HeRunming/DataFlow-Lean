import Mathlib

open scoped BigOperators
open MeasureTheory
open ProbabilityTheory

theorem variance_fin_average_iid
    {Ω : Type*} [MeasurableSpace Ω]
    (μprob : Measure Ω) [IsProbabilityMeasure μprob]
    {N : ℕ} (hN : 0 < N)
    (X : Fin N → Ω → ℝ)
    (mean sigma : ℝ)
    (h_indep : iIndepFun X μprob)
    (h_meas : ∀ i : Fin N, Measurable (X i))
    (h_memLp : ∀ i : Fin N, MemLp (X i) 2 μprob)
    (h_ident : ∀ i j : Fin N, IdentDistrib (X i) (X j) μprob μprob)
    (h_mean : ∀ i : Fin N, (∫ ω : Ω, X i ω ∂μprob) = mean)
    (h_variance : ∀ i : Fin N, ProbabilityTheory.variance (X i) μprob = sigma ^ 2) :
    ProbabilityTheory.variance
        (fun ω : Ω => (1 : ℝ) / (N : ℝ) * ((∑ i : Fin N, X i ω) : ℝ)) μprob =
      sigma ^ 2 / (N : ℝ) := by
  have hs := ProbabilityTheory.IndepFun.variance_sum
    (s := (Finset.univ : Finset (Fin N)))
    (fun i _ => h_memLp i) (fun i _ j _ hij => h_indep.indepFun hij)
  rw [ProbabilityTheory.variance_sum h_memLp] at hs
  rw [ProbabilityTheory.variance_const_mul, ProbabilityTheory.variance_fun_sum h_memLp, hs]
  simp only [h_variance, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  field_simp
