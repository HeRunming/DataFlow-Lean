import Mathlib

open scoped BigOperators

/-- The Frobenius inner product on real matrices. -/
def matrixInnerProduct {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  ∑ i : Fin m, (∑ j : Fin n, (A i j * B i j : ℝ) : ℝ)

theorem matrix_inner_product_eq_sum_eq_trace {m n : ℕ}
    (A B : Matrix (Fin m) (Fin n) ℝ) :
    matrixInnerProduct A B =
        (∑ i : Fin m, (∑ j : Fin n, (A i j * B i j : ℝ) : ℝ) : ℝ) ∧
      (∑ i : Fin m, (∑ j : Fin n, (A i j * B i j : ℝ) : ℝ) : ℝ) =
        (A.transpose * B).trace := by
  constructor
  · rfl
  · simp only [Matrix.trace, Matrix.mul_apply]
    rw [Finset.sum_comm]
    rfl
