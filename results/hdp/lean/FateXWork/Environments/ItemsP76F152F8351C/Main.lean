import Mathlib

open MeasureTheory ProbabilityTheory

namespace RandomVariableCorrelation

/-- Independent square-integrable random variables are uncorrelated. -/
theorem independent_random_variables_are_uncorrelated
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X Y : Ω → ℝ)
    (hX_measurable : Measurable X)
    (hY_measurable : Measurable Y)
    (hX_integrable : MemLp X (2 : ℕ) μ)
    (hY_integrable : MemLp Y (2 : ℕ) μ)
    (h_independent : IndepFun X Y μ) :
    covariance X Y μ = (0 : ℝ) := by
  sorry

/-- On a uniform four-point probability space, uncorrelatedness does not imply independence. -/
theorem uncorrelated_does_not_imply_independent_on_uniform_fin_four :
    let μ : Measure (Fin 4) :=
      ProbabilityTheory.uniformOn (Set.univ : Set (Fin 4))
    IsProbabilityMeasure μ ∧
      let X : Fin 4 → ℝ :=
        fun i => if i.val < 2 then (1 : ℝ) else (-1 : ℝ)
      let Y : Fin 4 → ℝ :=
        fun i => if i.val = 0 ∨ i.val = 3 then (1 : ℝ) else (-1 : ℝ)
      Measurable X ∧
      Measurable Y ∧
      MemLp X (2 : ℕ) μ ∧
      MemLp Y (2 : ℕ) μ ∧
      covariance X Y μ = (0 : ℝ) ∧
      ¬ IndepFun X Y μ := by
  sorry

end RandomVariableCorrelation
