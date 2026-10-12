import Mathlib

namespace SpectralStatement

def Symmetric {n : ℕ} (Sigma : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ i j : Fin n, Sigma i j = Sigma j i

def identityMatrix {n : ℕ} : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if i = j then (1 : ℝ) else (0 : ℝ)

def outerProduct {n : ℕ} (v : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => v i * v j

def rankOneTerm {n : ℕ} (a : ℝ) (v : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => a * v i * v j

def applyMatrix {n : ℕ} (Sigma : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) : Fin n → ℝ :=
  fun i => ∑ j : Fin n, (Sigma i j * v j : ℝ)

def OrthonormalBasis {n : ℕ} (v : Fin n → Fin n → ℝ) : Prop :=
  (∀ i : Fin n, (∑ j : Fin n, (v i j * v i j : ℝ)) = (1 : ℝ)) ∧
    (∀ i k : Fin n, i ≠ k →
      (∑ j : Fin n, (v i j * v k j : ℝ)) = (0 : ℝ)) ∧
    (∀ x : Fin n → ℝ, ∃ weights : Fin n → ℝ,
      ∀ j : Fin n, x j = ∑ i : Fin n, (weights i * v i j : ℝ))

private theorem symmetric_spectral_decomposition_hHerm
    {n : ℕ}
    (Sigma : Matrix (Fin n) (Fin n) ℝ)
    (hSigma : Symmetric Sigma) : Sigma.IsHermitian := by
  ext i j
  exact hSigma j i

private theorem eigenvector_basis_exists
    {n : ℕ}
    (Sigma : Matrix (Fin n) (Fin n) ℝ)
    (hSigma : Symmetric Sigma) :
    ∃ b : _root_.OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)), True := by
  classical
  let hHerm := symmetric_spectral_decomposition_hHerm Sigma hSigma
  exact ⟨hHerm.eigenvectorBasis, trivial⟩

private theorem unitary_columns_orthonormal
    {n : ℕ} (U : unitary (Matrix (Fin n) (Fin n) ℝ)) :
    ∀ i k : Fin n, ∑ j : Fin n, (U j i * U j k : ℝ) = if i = k then 1 else 0 := by
  intro i k
  have hU : (U : Matrix (Fin n) (Fin n) ℝ) ∈ unitary (Matrix (Fin n) (Fin n) ℝ) := U.property
  change star (U : Matrix (Fin n) (Fin n) ℝ) * U = 1 ∧
    U * star (U : Matrix (Fin n) (Fin n) ℝ) = 1 at hU
  have hentry := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i k) hU.1
  simpa [Matrix.mul_apply, Matrix.one_apply] using hentry

private theorem spectral_factor_mul_unitary
    {n : ℕ} {Sigma : Matrix (Fin n) (Fin n) ℝ}
    (U : unitary (Matrix (Fin n) (Fin n) ℝ))
    (coeff : Fin n → ℝ)
    (hSpec : Sigma = (U : Matrix (Fin n) (Fin n) ℝ) * Matrix.diagonal coeff * star (U : Matrix (Fin n) (Fin n) ℝ)) :
    Sigma * (U : Matrix (Fin n) (Fin n) ℝ) =
      (U : Matrix (Fin n) (Fin n) ℝ) * Matrix.diagonal coeff := by
  have hU : star (U : Matrix (Fin n) (Fin n) ℝ) * U = 1 := U.property.1
  rw [hSpec]
  rw [Matrix.mul_assoc]
  rw [hU]
  simp

private theorem unitary_coordinate_expansion
    {n : ℕ} (U : unitary (Matrix (Fin n) (Fin n) ℝ)) (x : Fin n → ℝ) :
    ∀ j : Fin n, x j = ∑ i : Fin n, (∑ k : Fin n, x k * U k i) * U j i := by
  intro j
  have hU : U * star (U : Matrix (Fin n) (Fin n) ℝ) = 1 := U.property.2
  calc
    x j = ∑ k : Fin n, x k * (if k = j then 1 else 0) := by simp
    _ = ∑ k : Fin n, x k * (∑ i : Fin n, U k i * U j i) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hkj := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M k j) hU
      symm
      simpa [Matrix.mul_apply, Matrix.one_apply] using congrArg (fun z : ℝ => x k * z) hkj
    _ = ∑ i : Fin n, (∑ k : Fin n, x k * U k i) * U j i := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k hk
      ring

private theorem unitary_outer_sum
    {n : ℕ} (U : unitary (Matrix (Fin n) (Fin n) ℝ)) :
    identityMatrix = ∑ i : Fin n, (outerProduct (fun j => U j i) : Matrix (Fin n) (Fin n) ℝ) := by
  ext i j
  have h := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i j) U.property.2
  simpa [identityMatrix, outerProduct, Matrix.mul_apply, Matrix.one_apply, Matrix.sum_apply] using h.symm

theorem symmetric_spectral_decomposition
    {n : ℕ}
    (Sigma : Matrix (Fin n) (Fin n) ℝ)
    (hSigma : Symmetric Sigma) :
    ∃ coeff : Fin n → ℝ, ∃ v : Fin n → Fin n → ℝ,
      OrthonormalBasis v ∧
        (∀ i : Fin n, ∀ j : Fin n,
          applyMatrix Sigma (v i) j = coeff i * v i j) ∧
        identityMatrix =
          ∑ i : Fin n, (outerProduct (v i) : Matrix (Fin n) (Fin n) ℝ) ∧
        Sigma =
          ∑ i : Fin n, (rankOneTerm (coeff i) (v i) : Matrix (Fin n) (Fin n) ℝ) := by
  classical
  let hHerm : Sigma.IsHermitian := symmetric_spectral_decomposition_hHerm Sigma hSigma
  let U := hHerm.eigenvectorUnitary
  let coeff : Fin n → ℝ := hHerm.eigenvalues
  let v : Fin n → Fin n → ℝ := fun i j => U j i
  have hSpec := hHerm.spectral_theorem
  have hDiag := spectral_factor_mul_unitary U coeff (by simpa [U, coeff] using hSpec)
  refine ⟨coeff, v, ?_, ?_, unitary_outer_sum U, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro i; simpa [v, U] using unitary_columns_orthonormal U i i
    · intro i k hik; simpa [v, U, hik] using unitary_columns_orthonormal U i k
    · intro x
      let w : Fin n → ℝ := fun i => ∑ k : Fin n, x k * U k i
      refine ⟨w, ?_⟩
      intro j
      simpa [w, v, U] using unitary_coordinate_expansion U x j
  · intro i j
    have hij := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M j i) hDiag
    simpa [applyMatrix, v, U, coeff, Matrix.mul_apply, Matrix.diagonal, mul_comm] using hij
  · ext i j
    simp only [Matrix.sum_apply, rankOneTerm]
    have hij := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i j) hSpec
    simpa [coeff, v, U, Matrix.mul_apply, Matrix.diagonal, mul_comm, mul_left_comm, mul_assoc] using hij

end SpectralStatement
