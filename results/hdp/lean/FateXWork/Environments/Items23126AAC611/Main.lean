import Mathlib

open MeasureTheory

 theorem bernoulli_sum_upper_tail
    {Ω : Type*} [MeasurableSpace Ω]
    (prob : Measure Ω) [IsProbabilityMeasure prob]
    (N : ℕ)
    (X : Fin N → Ω → ℝ)
    (p : Fin N → NNReal)
    (h_p : ∀ i : Fin N, p i ≤ (1 : NNReal))
    (h_meas : ∀ i : Fin N, Measurable (X i))
    (h_support : ∀ i : Fin N,
      ∀ᵐ ω ∂prob, X i ω = (0 : ℝ) ∨ X i ω = (1 : ℝ))
    (h_param : ∀ i : Fin N,
      ENNReal.toReal (prob {ω : Ω | X i ω = (1 : ℝ)}) = (p i : ℝ))
    (h_indep : ProbabilityTheory.iIndepFun X prob)
    (h_integrable : Integrable
      (fun ω : Ω => ∑ i : Fin N, (X i ω : ℝ)) prob)
    (μ : ℝ)
    (h_mean : μ = ∫ ω : Ω, (∑ i : Fin N, (X i ω : ℝ)) ∂prob) :
    ∀ t : ℝ, μ ≤ t → 0 < t →
      ENNReal.toReal (prob {ω : Ω | (∑ i : Fin N, (X i ω : ℝ)) ≥ t}) ≤
        Real.exp (-μ) *
          Real.rpow (Real.exp (1 : ℝ) * μ / t) t := by
  sorry
