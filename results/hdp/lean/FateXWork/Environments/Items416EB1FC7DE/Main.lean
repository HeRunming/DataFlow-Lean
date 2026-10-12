import Mathlib

open scoped BigOperators

namespace SourceCF

/-- The Euclidean unit sphere of a real coordinate subspace. -/
def unitSphere {n : ℕ} (E : Submodule ℝ (Fin n → ℝ)) :
    Set (Fin n → ℝ) :=
  {x | x ∈ E ∧ (∑ i : Fin n, (x i) ^ 2 : ℝ) = (1 : ℝ)}

/-- The quadratic form xᵀ A x, written in coordinates. -/
def quadraticForm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (x : Fin n → ℝ) : ℝ :=
  (∑ i : Fin n, (∑ j : Fin n, x i * A i j * x j : ℝ) : ℝ)

/-- An attained minimum on the Euclidean unit sphere. -/
def sphereMinimum {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (E : Submodule ℝ (Fin n → ℝ)) (value : ℝ) : Prop :=
  (∃ x : Fin n → ℝ,
    x ∈ unitSphere E ∧ quadraticForm A x = value) ∧
  (∀ x : Fin n → ℝ,
    x ∈ unitSphere E → value ≤ quadraticForm A x)

/-- An attained maximum on the Euclidean unit sphere. -/
def sphereMaximum {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (E : Submodule ℝ (Fin n → ℝ)) (value : ℝ) : Prop :=
  (∃ x : Fin n → ℝ,
    x ∈ unitSphere E ∧ quadraticForm A x = value) ∧
  (∀ x : Fin n → ℝ,
    x ∈ unitSphere E → quadraticForm A x ≤ value)

/-- The attained maximum of the sphere minima over all d-dimensional subspaces. -/
def maxMinAt {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (d : ℕ) (value : ℝ) : Prop :=
  (∃ E : Submodule ℝ (Fin n → ℝ),
    Module.finrank ℝ E = d ∧ sphereMinimum A E value) ∧
  (∀ E : Submodule ℝ (Fin n → ℝ),
    Module.finrank ℝ E = d →
      ∃ minimum : ℝ, sphereMinimum A E minimum ∧ minimum ≤ value)

/-- The attained minimum of the sphere maxima over all d-dimensional subspaces. -/
def minMaxAt {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (d : ℕ) (value : ℝ) : Prop :=
  (∃ E : Submodule ℝ (Fin n → ℝ),
    Module.finrank ℝ E = d ∧ sphereMaximum A E value) ∧
  (∀ E : Submodule ℝ (Fin n → ℝ),
    Module.finrank ℝ E = d →
      ∃ maximum : ℝ, sphereMaximum A E maximum ∧ value ≤ maximum)

/--
The eigenvalue at zero-based descending rank k, counting multiplicities.
The coordinate conditions specify n orthonormal eigenvectors and their
nonincreasing list of real eigenvalues, without choosing a spectral API.
-/
def isKthLargestEigenvalue {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (k : Fin n) (value : ℝ) : Prop :=
  ∃ coeff : Fin n → ℝ, ∃ v : Fin n → Fin n → ℝ,
    (∀ i j : Fin n,
      (∑ p : Fin n, v i p * v j p : ℝ) =
        (if i = j then (1 : ℝ) else (0 : ℝ))) ∧
    (∀ j r : Fin n,
      (∑ c : Fin n, A r c * v j c : ℝ) = coeff j * v j r) ∧
    (∀ i j : Fin n, i.val ≤ j.val → coeff j ≤ coeff i) ∧
    value = coeff k

/-- Courant–Fischer: source rank k.val + 1, with both extrema attained. -/
theorem courant_fischer {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i j : Fin n, A i j = A j i)
    (k : Fin n) :
    ∃ value : ℝ,
      isKthLargestEigenvalue A k value ∧
      maxMinAt A (k.val + 1) value ∧
      minMaxAt A (n - (k.val + 1) + 1) value := by sorry

end SourceCF
