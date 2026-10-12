import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.Matrix.Order

/-- (a) The Gram matrix of any finite family of vectors is symmetric and positive-semidefinite. -/
theorem gram_matrix_symmetric_posSemidef
    {ι : Type*} [Fintype ι]
    {E : Type*} [SeminormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (v : ι → E) :
    Matrix.transpose (Matrix.gram ℝ v) = Matrix.gram ℝ v ∧
      (Matrix.gram ℝ v).PosSemidef := by
  constructor
  · ext i j
    simp [Matrix.gram, real_inner_comm]
  · exact Matrix.posSemidef_gram ℝ v

private theorem gram_of_factor {n : ℕ} (A M : Matrix (Fin n) (Fin n) ℝ)
    (h : A.transpose * A = M) :
    ∃ v : Fin n → EuclideanSpace ℝ (Fin n), Matrix.gram ℝ v = M := by
  refine ⟨fun i => WithLp.toLp 2 (fun k => A k i), ?_⟩
  rw [← h]
  ext i j
  simp [Matrix.gram, Matrix.mul_apply, PiLp.inner_apply, dotProduct, mul_comm]

open scoped MatrixOrder in
private theorem sqrt_factor {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (h_psd : M.PosSemidef) :
    Matrix.transpose (CFC.sqrt M) * CFC.sqrt M = M := by
  have ht : Matrix.transpose (CFC.sqrt M) = CFC.sqrt M := by
    have h := (CFC.sqrt_nonneg M).1
    simpa only [sub_zero, Matrix.IsHermitian] using h
  rw [ht]
  exact CFC.sqrt_mul_sqrt_self M h_psd.nonneg

open scoped MatrixOrder

/-- (b) Every symmetric positive-semidefinite real matrix is a Gram matrix. -/
theorem symmetric_posSemidef_is_gram_matrix
    {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ)
    (h_symm : Matrix.transpose M = M)
    (h_psd : M.PosSemidef) :
    ∃ v : Fin n → EuclideanSpace ℝ (Fin n),
      Matrix.gram ℝ v = M := by
  classical
  have _h_symm := h_symm
  refine gram_of_factor (CFC.sqrt M) M ?_
  simpa only using sqrt_factor M h_psd
