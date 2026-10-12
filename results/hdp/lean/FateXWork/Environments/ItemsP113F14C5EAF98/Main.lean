import Mathlib

open scoped BigOperators

namespace FrobeniusIdentity

/-- The real Frobenius norm, defined entrywise rather than through a matrix norm instance. -/
noncomputable def frobeniusNorm {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  Real.sqrt ((∑ i : Fin m, ∑ j : Fin n, (A i j) ^ (2 : ℕ)) : ℝ)

/-- The real matrix inner product, defined entrywise. -/
def matrixInner {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  ((∑ i : Fin m, ∑ j : Fin n, A i j * B i j) : ℝ)

/-- Equation (4.8). -/
theorem frobenius_norm_sq_eq_inner_eq_trace
    (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) :
    frobeniusNorm A ^ (2 : ℕ) = matrixInner A A ∧
      matrixInner A A = Matrix.trace (A.transpose * A) := by
  constructor
  · unfold frobeniusNorm matrixInner
    rw [Real.sq_sqrt]
    · simp only [pow_two]
    · positivity
  · unfold matrixInner
    change (∑ i : Fin m, ∑ j : Fin n, A i j * A i j) =
      ∑ i : Fin n, ∑ j : Fin m, A j i * A j i
    rw [Finset.sum_comm]

end FrobeniusIdentity
