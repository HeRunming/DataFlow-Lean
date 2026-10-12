import Mathlib

open scoped BigOperators

namespace SourceFormalization

/-- A real square matrix is orthogonal when its transpose is both a left and right inverse. -/
def IsOrthogonal {n : ℕ} (U : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  U.transpose * U = (1 : Matrix (Fin n) (Fin n) ℝ) ∧
    U * U.transpose = (1 : Matrix (Fin n) (Fin n) ℝ)

/-- The rectangular diagonal matrix with entries `s i` on the diagonal. -/
def RectDiagonal {m n : ℕ} (s : ℕ → ℝ) : Matrix (Fin m) (Fin n) ℝ :=
  fun i j => if i.val = j.val then s i.val else (0 : ℝ)

/-- The diagonal matrix whose diagonal entries are given by `coeff`. -/
def DiagonalMatrix {n : ℕ} (coeff : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if i = j then coeff i else (0 : ℝ)

/-- The pointwise spectral sum associated with columns of `U` and coefficients `coeff`. -/
def SpectralSum {n : ℕ} (U : Matrix (Fin n) (Fin n) ℝ)
    (coeff : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  ∑ i : Fin n, coeff i • (fun j k => U j i * U k i)

theorem singular_value_decomposition_rewrite
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    ∃ (r : ℕ) (s : ℕ → ℝ)
      (U : Matrix (Fin m) (Fin m) ℝ)
      (V : Matrix (Fin n) (Fin n) ℝ)
      (Sigma : Matrix (Fin m) (Fin n) ℝ),
      r ≤ min m n ∧
      (∀ i : ℕ, i < r → (0 : ℝ) < s i) ∧
      (∀ i : ℕ, r ≤ i → s i = (0 : ℝ)) ∧
      (∀ i j : ℕ, i ≤ j → s j ≤ s i) ∧
      Sigma = RectDiagonal s ∧
      IsOrthogonal U ∧
      IsOrthogonal V ∧
      A = U * Sigma * V.transpose := by
  sorry

theorem symmetric_matrix_spectral_decomposition
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i j : Fin n, A i j = A j i) :
    ∃ (coeff : Fin n → ℝ)
      (U : Matrix (Fin n) (Fin n) ℝ)
      (Lambda : Matrix (Fin n) (Fin n) ℝ),
      IsOrthogonal U ∧
      Lambda = DiagonalMatrix coeff ∧
      A = SpectralSum U coeff ∧
      A = U * Lambda * U.transpose := by
  sorry

end SourceFormalization
