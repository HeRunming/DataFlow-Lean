import Mathlib

/-!
# Exercise 1.14: expectations and finite ℓᵖ norms

This module states the finite-exponent part of source exercise 1.14 for
nonnegative, extended-real-valued random variables. The source endpoint
`p = ∞` requires a separate essential-supremum formulation and is not included.
-/

open scoped ENNReal NNReal
open MeasureTheory

namespace FateXWork.Environments.Items1143C9DEB84

/-- The `p`-th root of the sum of the entries of a finite `ℝ≥0∞`-valued vector. -/
noncomputable def finiteLpRoot {n : ℕ} (p : ℝ) (v : Fin n → ℝ≥0∞) : ℝ≥0∞ :=
  (∑ i, v i).rpow p⁻¹

/--
Source exercise 1.14, restricted to finite exponents: for a finite family of
nonnegative random variables and `1 ≤ p`, the ℓᵖ norm of their expectations is
at most the expectation of their pointwise ℓᵖ norm, which is at most the ℓᵖ
norm formed from their `p`-th moments.

Proof sketch: the first inequality is Jensen's inequality for the convex finite
ℓᵖ norm (or Minkowski applied to integration). The second is the integral form
of Minkowski's inequality. Work with `ENNReal.rpow` and `lintegral`; the cases
`n = 0` and `p = 1` may be separated if strict library hypotheses require it.
-/
theorem exercise_1_14_finite
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (μ : Measure Ω)
    (X : Fin n → Ω → ℝ≥0∞) (p : ℝ) (hp : 1 ≤ p)
    (hX : ∀ i, AEMeasurable (X i) μ) :
    finiteLpRoot p (fun i => (∫⁻ x, X i x ∂μ).rpow p) ≤
        ∫⁻ x, finiteLpRoot p (fun i => (X i x).rpow p) ∂μ ∧
      (∫⁻ x, finiteLpRoot p (fun i => (X i x).rpow p) ∂μ) ≤
        finiteLpRoot p (fun i => ∫⁻ x, (X i x).rpow p ∂μ) := by
  sorry

end FateXWork.Environments.Items1143C9DEB84
