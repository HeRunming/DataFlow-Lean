import Mathlib

open MeasureTheory ProbabilityTheory

/--
Source proof: the source states Hoeffding's exponential tail bound for a finite
family of independent variables. The standard prover route is to apply the
bounded-variable subgaussian MGF estimate to each centered variable and then
use the independent-sum tail bound, followed by arithmetic normalization of the
resulting parameter.
Prover notes: expectations are represented by Bochner integrals; use the
subgaussian results in `Mathlib.Probability.Moments.SubGaussian`.
-/
theorem hoeffding_bound_for_bounded_independent
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {N : ℕ} (X : Fin N → Ω → ℝ)
    (a b : Fin N → ℝ)
    (h_indep : iIndepFun X μ)
    (h_meas : ∀ i, AEMeasurable (X i) μ)
    (h_bounds : ∀ i, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc (a i) (b i))
    {t : ℝ} (ht : 0 < t) :
    μ.real {ω | t ≤ ∑ i, (X i ω - ∫ x, X i x ∂μ)} ≤
      Real.exp (-2 * t ^ 2 / ∑ i, (b i - a i) ^ 2) := by
  sorry
