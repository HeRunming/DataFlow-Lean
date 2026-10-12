import Mathlib

open MeasureTheory

 theorem bernstein_inequality
    {Ω : Type*}
    [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    (N : ℕ)
    (X : Fin N → Ω → ℝ)
    (K : ℝ)
    (h_indep : ProbabilityTheory.iIndepFun X μ)
    (h_meas : ∀ i : Fin N, Measurable (X i))
    (h_integrable :
      ∀ i : Fin N, MeasureTheory.Integrable (X i) μ)
    (h_sq_integrable :
      ∀ i : Fin N,
        MeasureTheory.Integrable
          (fun ω : Ω => (X i ω) ^ (2 : ℕ)) μ)
    (h_mean :
      ∀ i : Fin N,
        (MeasureTheory.integral μ (fun ω : Ω => X i ω) : ℝ) = (0 : ℝ))
    (h_bound :
      ∀ i : Fin N, ∀ ω : Ω, |X i ω| ≤ K)
    (t : ℝ)
    (ht : (0 : ℝ) ≤ t) :
    let sigmaSq : ℝ :=
      ((∑ i : Fin N,
          (MeasureTheory.integral μ
            (fun ω : Ω => (X i ω) ^ (2 : ℕ)) : ℝ)) : ℝ)
    μ {ω : Ω | |(∑ i : Fin N, X i ω)| ≥ t} ≤
      ENNReal.ofReal
        ((2 : ℝ) *
          Real.exp
            (-(((t ^ (2 : ℕ)) / (2 : ℝ)) /
              (sigmaSq + K * t / (3 : ℝ))))) := by
  sorry
