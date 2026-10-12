import Mathlib

open MeasureTheory ProbabilityTheory

namespace HoeffdingExcerpt

/-- The single-term tail condition in (2.15), imposed on every summand. -/
def HasSingleTermTailBound
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {n : ℕ} (X : Fin n → Ω → ℝ) (c : ℝ) : Prop :=
  ∀ i : Fin n, ∀ t : ℝ, 0 ≤ t →
    μ.real {ω : Ω | t ≤ |X i ω|} ≤
      (2 : ℝ) * Real.exp (-c * t ^ 2)

/-- The weighted finite-sum tail inequality corresponding to (2.14),
for the same family of summands. -/
def HasWeightedHoeffdingTailBound
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {n : ℕ} (X : Fin n → Ω → ℝ) (c : ℝ) : Prop :=
  ∀ (a : Fin n → ℝ) (t : ℝ),
    0 ≤ t →
    0 < ((∑ i : Fin n, ((a i) ^ 2 : ℝ)) : ℝ) →
    μ.real {ω : Ω |
      t ≤ |((∑ i : Fin n, (a i * X i ω : ℝ)) : ℝ)|} ≤
      (2 : ℝ) * Real.exp
        (-c * t ^ 2 / ((∑ i : Fin n, ((a i) ^ 2 : ℝ)) : ℝ))

/-- The condition in (2.15) is sufficient for the corresponding weighted-sum
Hoeffding inequality for the same independent, centered family. -/
theorem single_term_tail_bound_sufficient
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n : ℕ} {X : Fin n → Ω → ℝ} {c : ℝ}
    (hc : 0 < c)
    (hX : HasSingleTermTailBound μ X c)
    (h_indep : ProbabilityTheory.iIndepFun X μ)
    (h_integrable : ∀ i : Fin n, Integrable (X i) μ)
    (h_centered : ∀ i : Fin n, ∫ ω, X i ω ∂μ = (0 : ℝ)) :
    ∃ c' : ℝ, 0 < c' ∧ HasWeightedHoeffdingTailBound μ X c' := by
  sorry

end HoeffdingExcerpt
