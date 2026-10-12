import Mathlib

/-!
Formalization of HDP exercise 4.13 (Davis–Kahan for the top eigenspaces).
-/

namespace FateXWork.Environments.Items413BDE94DB1

noncomputable section

def outerProduct {n : ℕ} (u : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => u i * u j

def matrixNorm {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, |M i j|

def topSpectralProjection {n : ℕ} (k : ℕ)
    (u : Fin n → Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  ∑ i : Fin n, if i.val < k then outerProduct (u i) else 0

/--
Source proof: no proof text is supplied; the exercise refers to Davis–Kahan
(Theorem 4.1.15). Prover notes: use the eigenvector equations and separation
across the spectral gap to control cross terms, then apply orthonormality and
the operator-norm triangle inequality. This finite-matrix statement makes the
spectral decompositions and ordered eigenvalue data explicit.
-/
theorem davisKahan_top_spectral_projections {n k : ℕ} (hkn : k ≤ n)
    (A B : Matrix (Fin n) (Fin n) ℝ)
    (eigenA eigenB : Fin n → ℝ) (u v : Fin n → Fin n → ℝ)
    (hA_symm : A.IsSymm) (hB_symm : B.IsSymm)
    (hA_decomp : A = ∑ i : Fin n, (eigenA i) • outerProduct (u i))
    (hB_decomp : B = ∑ i : Fin n, (eigenB i) • outerProduct (v i))
    (hA_order : ∀ i j : Fin n, i.val ≤ j.val → eigenA j ≤ eigenA i)
    (hB_order : ∀ i j : Fin n, i.val ≤ j.val → eigenB j ≤ eigenB i)
    (horth_u : ∀ i j : Fin n, i ≠ j → ∑ r : Fin n, u i r * u j r = 0)
    (horth_v : ∀ i j : Fin n, i ≠ j → ∑ r : Fin n, v i r * v j r = 0)
    (δ : ℝ) (hδ : 0 < δ)
    (hsep : ∀ i j : Fin n, i.val < k → j.val ≥ k →
      δ ≤ |eigenA i - eigenB j|) :
    matrixNorm (topSpectralProjection k u - topSpectralProjection k v) ≤
      2 * matrixNorm (A - B) / δ := by
  sorry

end
end FateXWork.Environments.Items413BDE94DB1
