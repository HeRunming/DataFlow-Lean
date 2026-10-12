import Mathlib

open MeasureTheory ProbabilityTheory

private def headsIndicator {Ω : Type*} {N : ℕ}
    (heads : Fin N → Ω → Bool) (i : Fin N) (ω : Ω) : ℝ :=
  if heads i ω then (1 : ℝ) else (0 : ℝ)

private def headsCount {Ω : Type*} {N : ℕ}
    (heads : Fin N → Ω → Bool) (ω : Ω) : ℝ :=
  ((Finset.univ.filter (fun i : Fin N => heads i ω = true)).card : ℝ)

theorem heads_count_eq_sum_of_bernoulli_indicators
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (N : ℕ) (heads : Fin N → Ω → Bool)
    (hmeas : ∀ i : Fin N, Measurable (headsIndicator heads i))
    (hindep : ProbabilityTheory.iIndepFun
      (fun i : Fin N => headsIndicator heads i) μ)
    (hhalf : ∀ i : Fin N,
      μ {ω : Ω | headsIndicator heads i ω = (1 : ℝ)} = (1 / 2 : ENNReal)) :
    ∀ ω : Ω,
      headsCount heads ω =
        (Finset.univ.sum (fun i : Fin N => headsIndicator heads i ω) : ℝ) := by
  sorry
