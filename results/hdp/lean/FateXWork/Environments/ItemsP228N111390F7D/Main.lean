import Mathlib

open scoped BigOperators

/-- The Frobenius inner product of two real square matrices. -/
def matrixInner (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, A i j * B i j

 theorem matrix_inner_eq_trace_transpose_mul (n : ℕ)
    (A B : Matrix (Fin n) (Fin n) ℝ) :
    matrixInner n A B = Matrix.trace (Matrix.transpose A * B) := by
  classical
  simp only [matrixInner, Matrix.trace, Matrix.mul_apply, Matrix.transpose_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  simp [Matrix.transpose_apply, mul_comm]
