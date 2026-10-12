import Mathlib

/-!
# Davis–Kahan inequality for spectral projections

This file records the finite-dimensional real matrix formulation of source Lemma
4.1.16. The source entry supplies the statement but no proof text.
-/

namespace FateXWork.Environments.Items411625875953

noncomputable section

/-- The rank-one matrix `u uᵀ` associated to a vector indexed by `Fin n`. -/
noncomputable def outerProduct {n : ℕ} (u : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => u i * u j

noncomputable def matrixNorm {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, |M i j|

/-- The spectral projection obtained by summing `uᵢuᵢᵀ` over eigenvalues in `I`. -/
noncomputable def spectralProjection {n : ℕ} (eigvals : Fin n → ℝ) (u : Fin n → Fin n → ℝ)
    (I : Set ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  ∑ i : Fin n, I.indicator (fun _ => outerProduct (u i)) (eigvals i)

/--
Source proof: the source provides no proof text. The standard Davis–Kahan
argument applies the eigenvector equations to bound cross terms across the
spectral gap, then uses orthonormality to obtain the operator-norm estimate.
Prover notes: search Mathlib's finite-dimensional spectral and orthogonal
projection APIs; the hypotheses unpack the source's spectral decompositions.
-/
lemma davisKahan_spectralProjection {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ)
    (eigvalsA eigvalsB : Fin n → ℝ) (u v : Fin n → Fin n → ℝ)
    (I J : Set ℝ) (δ : ℝ)
    (hA_symm : A.IsSymm) (hB_symm : B.IsSymm)
    (hA_decomp : A = ∑ i : Fin n, (eigvalsA i) • outerProduct (u i))
    (hB_decomp : B = ∑ j : Fin n, (eigvalsB j) • outerProduct (v j))
    (hI_interval : Set.OrdConnected I)
    (hsep : ∀ (i j : Fin n), eigvalsA i ∈ I → eigvalsB j ∈ J →
      δ ≤ |eigvalsA i - eigvalsB j|)
    (hδ : 0 < δ) :
    matrixNorm ((spectralProjection eigvalsB v J) * (spectralProjection eigvalsA u I)) ≤
      matrixNorm (A - B) / δ := by
  sorry

end
end FateXWork.Environments.Items411625875953
