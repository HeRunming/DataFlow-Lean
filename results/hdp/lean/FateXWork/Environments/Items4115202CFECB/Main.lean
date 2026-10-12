import Mathlib

/-- Real symmetric matrices, represented by matrices whose transpose equals themselves. -/
def SymmetricMatrix (n : ℕ) := {A : Matrix (Fin n) (Fin n) ℝ // A.IsSymm}

/-- Finite spectral data with decreasing eigenvalues and normalized eigenvectors.
The decomposition equation is supplied separately when it is needed. -/
structure SpectralData (n : ℕ) where
  eigenvalue : Fin n → ℝ
  eigenvector : Fin n → (Fin n → ℝ)
  ordered : ∀ i j, i.val ≤ j.val → eigenvalue j ≤ eigenvalue i
  unit : ∀ i, ∑ j, eigenvector i j ^ 2 = 1

/--
Source proof: no proof text is included in the source QA entry; the standard
Davis--Kahan argument projects the perturbed eigenvector onto the orthogonal
complement of the isolated eigendirection and uses the spectral gap.
Prover notes: use the spectral gap to lower-bound the complementary component
and bound the residual by the perturbation norm; the principal-angle convention
handles sign ambiguity and gives the factor 2.
-/
theorem davis_kahan_inequality (n : ℕ) (A B : SymmetricMatrix n)
    (eigA eigB : Fin n → ℝ) (u v : Fin n → (Fin n → ℝ)) (k : Fin n)
    (δ θ : ℝ)
    (hδ : 0 < δ)
    (hsep : ∀ i : Fin n, i ≠ k → δ ≤ |eigA k - eigA i|)
    (hangle : 0 ≤ θ ∧ θ ≤ Real.pi / 2)
    (hprincipal : θ = Real.arccos |∑ i, u k i * v k i|)
    (ε : ℝ) (hε : 0 ≤ ε) :
    Real.sin θ ≤ 2 * ε / δ := by
  sorry
