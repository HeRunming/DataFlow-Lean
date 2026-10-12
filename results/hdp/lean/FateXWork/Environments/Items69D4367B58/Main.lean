import Mathlib

open scoped BigOperators ENNReal
open MeasureTheory

namespace FateXWork.Environments.Items69D4367B58

/-- Euclidean norm of a finite real vector. -/
noncomputable def euclideanNorm {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  Real.sqrt (∑ i, (x i) ^ 2)

/-- Frobenius norm of a finite real matrix. -/
noncomputable def matrixFrobeniusNorm {m n : ℕ} (B : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  Real.sqrt (∑ i, ∑ j, (B i j) ^ 2)

/-- Induced Euclidean operator norm, written as a supremum over the unit ball. -/
noncomputable def matrixOperatorNorm {m n : ℕ} (B : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  sSup {r : ℝ | ∃ x : Fin n → ℝ, euclideanNorm x ≤ 1 ∧
    r = euclideanNorm (B.mulVec x)}

/-- A concrete directional-MGF convention for the vector ψ₂ bound. -/
def HasPsiTwoNormAtMost {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (X : Ω → Fin n → ℝ) (K : ℝ) (μ : Measure Ω) : Prop :=
  ∀ u : Fin n → ℝ, euclideanNorm u ≤ 1 →
    ∫ ω, Real.exp (((∑ i, X ω i * u i) ^ 2) / K ^ 2) ∂μ ≤ 2

/--
Exercise 6.9 (MGF of the squared norm).

Source proof: the source supplies only the exercise statement, not a proof.
Proof sketch: linearize the squared exponential with an auxiliary Gaussian, apply
the directional ψ₂ estimate to `⟪X, Bᵀg⟫`, and bound the resulting Gaussian
quadratic exponential by the Frobenius and operator norms.
Prover notes: use `hλ` to absorb the operator-norm term in the Gaussian
quadratic estimate; the remaining trace term is bounded by the Frobenius norm.
-/
theorem mgf_squared_norm_of_subgaussian_vector :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        {m n : ℕ} (B : Matrix (Fin m) (Fin n) ℝ) (X : Ω → Fin n → ℝ)
        (K t : ℝ),
        0 < K →
        (∀ i, AEStronglyMeasurable (fun ω => X ω i) μ) →
        (∀ i, Integrable (fun ω => X ω i) μ) →
        (∀ i, ∫ ω, X ω i ∂μ = 0) →
        HasPsiTwoNormAtMost X K μ →
        |t| ≤ c / (K * matrixOperatorNorm B) →
        ∫ ω, Real.exp (t ^ 2 * (euclideanNorm (B.mulVec (X ω))) ^ 2) ∂μ ≤
          Real.exp (C * K ^ 2 * t ^ 2 * (matrixFrobeniusNorm B) ^ 2) := by
  sorry

end FateXWork.Environments.Items69D4367B58
