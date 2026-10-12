import Mathlib

namespace CourantFischerStatement

noncomputable def l2Norm {n : ℕ} (v : Fin n → ℝ) : ℝ :=
  Real.sqrt
    (((Finset.univ : Finset (Fin n)).sum
      (fun i : Fin n => (v i) ^ (2 : ℕ))) : ℝ)

def dotProduct {n : ℕ} (v w : Fin n → ℝ) : ℝ :=
  (((Finset.univ : Finset (Fin n)).sum
    (fun i : Fin n => v i * w i)) : ℝ)

def IsSymmetricMatrix {n : ℕ} (sigma : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ i j : Fin n, sigma i j = sigma j i

def IsEigenvector {n : ℕ} (sigma : Matrix (Fin n) (Fin n) ℝ)
    (eigenvalue : ℝ) (v : Fin n → ℝ) : Prop :=
  Matrix.mulVec sigma v = eigenvalue • v

def IsUnitVector {n : ℕ} (v : Fin n → ℝ) : Prop :=
  l2Norm v = (1 : ℝ)

def OrthogonalToPrevious {n : ℕ}
    (eigenvectors : Fin n → Fin n → ℝ) (k : Fin n) (v : Fin n → ℝ) : Prop :=
  ∀ i : Fin n, i.val < k.val →
    dotProduct v (eigenvectors i) = (0 : ℝ)

def PairwiseOrthogonal {n : ℕ}
    (eigenvectors : Fin n → Fin n → ℝ) : Prop :=
  ∀ i j : Fin n, i ≠ j →
    dotProduct (eigenvectors i) (eigenvectors j) = (0 : ℝ)

def Feasible {n : ℕ}
    (eigenvectors : Fin n → Fin n → ℝ) (k : Fin n) (v : Fin n → ℝ) : Prop :=
  OrthogonalToPrevious eigenvectors k v ∧ IsUnitVector v

def rayleighQuotient {n : ℕ}
    (sigma : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) : ℝ :=
  (((Finset.univ : Finset (Fin n)).sum
    (fun i : Fin n => v i * (Matrix.mulVec sigma v) i)) : ℝ)

def RayleighValues {n : ℕ}
    (sigma : Matrix (Fin n) (Fin n) ℝ)
    (eigenvectors : Fin n → Fin n → ℝ) (k : Fin n) : Set ℝ :=
  {q : ℝ | ∃ v : Fin n → ℝ,
    Feasible eigenvectors k v ∧ q = rayleighQuotient sigma v}

theorem courants_fischer_maximum
    {n : ℕ}
    (sigma : Matrix (Fin n) (Fin n) ℝ)
    (eigenvalues : Fin n → ℝ)
    (eigenvectors : Fin n → Fin n → ℝ)
    (hSymmetric : IsSymmetricMatrix sigma)
    (hEigenvector : ∀ i : Fin n,
      IsEigenvector sigma (eigenvalues i) (eigenvectors i))
    (hUnit : ∀ i : Fin n, IsUnitVector (eigenvectors i))
    (hOrthonormal : PairwiseOrthogonal eigenvectors)
    (hOrdered : ∀ i j : Fin n, i.val ≤ j.val → eigenvalues j ≤ eigenvalues i) :
    ∀ k : Fin n,
      IsGreatest (RayleighValues sigma eigenvectors k) (eigenvalues k) ∧
        Feasible eigenvectors k (eigenvectors k) ∧
        rayleighQuotient sigma (eigenvectors k) = eigenvalues k := by
  sorry

end CourantFischerStatement
