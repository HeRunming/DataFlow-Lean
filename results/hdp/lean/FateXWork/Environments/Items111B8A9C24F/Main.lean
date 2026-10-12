import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

open MeasureTheory
open scoped ENNReal

namespace FateXWork.Environments.Items111B8A9C24F

/-!
Source proof: apply the standard monotonicity theorem for the normalized
Lᵖ seminorm on a probability space, with the endpoint cases included.
Prover notes: `eLpNorm_le_eLpNorm_of_exponent_le` is the intended Mathlib
lemma; `hX.aestronglyMeasurable` supplies its measurability hypothesis.
-/
theorem lpNorm_mono
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : Measurable X)
    {p q : ℝ≥0∞} (hp : 0 ≤ p) (hpq : p ≤ q) (hq : q ≤ ∞) :
    eLpNorm X p μ ≤ eLpNorm X q μ := by
  sorry

/-!
Source proof: choose a heavy-tailed random variable on a countable
probability space whose p-moment is finite and q-moment is infinite.
Prover notes: the intended witness has sample space `ℕ`; the construction
must establish the probability, measurability, and two endpoint norm claims.
-/
theorem lpNorm_not_reverse
    (p q : ℝ≥0∞) (hp : 0 ≤ p) (hpq : p < q) (hq : q ≤ ∞) :
    ∃ (μ : Measure ℕ) (X : ℕ → ℝ),
      IsProbabilityMeasure μ ∧
      Measurable X ∧
      eLpNorm X p μ < ∞ ∧
      eLpNorm X q μ = ∞ := by
  sorry

end FateXWork.Environments.Items111B8A9C24F
