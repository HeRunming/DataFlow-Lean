import Mathlib

/-! Formalization of Exercise 4.2, "Basic properties of the operator norm".
The source's Definition 4.1.8 is not included in this QA slice; the displayed
functional is therefore an explicitly provisional entrywise matrix norm. -/

def matrixOperatorNorm {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) : ℝ := ∑ i, ∑ j, ‖A i j‖

/-- Source proof: verify definiteness, triangle, and absolute homogeneity.
Prover notes: this states the norm axioms for the provisional entrywise
functional; replace it by the Definition 4.1.8 operator norm when available. -/
theorem matrixOperatorNorm_isNorm (m n : ℕ) :
    matrixOperatorNorm (0 : Matrix (Fin m) (Fin n) ℝ) = 0 ∧
      (∀ (A : Matrix (Fin m) (Fin n) ℝ), matrixOperatorNorm (-A) = matrixOperatorNorm A) ∧
      (∀ (A B : Matrix (Fin m) (Fin n) ℝ), matrixOperatorNorm (A + B) ≤
        matrixOperatorNorm A + matrixOperatorNorm B) ∧
      (∀ (c : ℝ) (A : Matrix (Fin m) (Fin n) ℝ), matrixOperatorNorm (c • A) = |c| * matrixOperatorNorm A) ∧
      (∀ (A : Matrix (Fin m) (Fin n) ℝ), matrixOperatorNorm A = 0 ↔ A = 0) := by sorry

/-- Source proof: transpose exchanges row and column coordinates and preserves
the norm. Prover notes: this is for the provisional entrywise norm. -/
theorem matrixOperatorNorm_transpose (m n : ℕ)
    (A : Matrix (Fin m) (Fin n) ℝ) :
    matrixOperatorNorm A = matrixOperatorNorm A.transpose := by sorry

/-- Source proof: bound `B x` first and then apply the operator bound for `A`.
Prover notes: dependent indices express compatible dimensions; for this
provisional norm, use the usual finite-sum estimate. -/
theorem matrixOperatorNorm_mul_le {m n k : Type*}
    [Fintype m] [Fintype n] [Fintype k]
    (A : Matrix m n ℝ) (B : Matrix n k ℝ) :
    matrixOperatorNorm (A * B) ≤ matrixOperatorNorm A * matrixOperatorNorm B := by sorry

/-- Source proof: choose nonzero factors with a nontrivial kernel, so the product is zero while both norms are positive. Prover notes: this records the requested example as an existence statement. -/
theorem matrixOperatorNorm_mul_zero_right_factor_example :
    ∃ (A B : Matrix (Fin 2) (Fin 2) ℝ),
      A * B = 0 ∧ 0 < matrixOperatorNorm A * matrixOperatorNorm B := by sorry

/-- Source proof: restrict to selected rows and columns; restriction cannot
increase the norm. Prover notes: injective maps represent a genuine selected
submatrix (arbitrary maps could repeat entries and make the claim false). -/
theorem matrixOperatorNorm_submatrix_le {m n M N : Type*}
    [Fintype m] [Fintype n] [Fintype M] [Fintype N]
    (A : Matrix M N ℝ) (i : m → M) (j : n → N)
    (hi : Function.Injective i) (hj : Function.Injective j) :
    matrixOperatorNorm (A.submatrix i j) ≤ matrixOperatorNorm A := by sorry
