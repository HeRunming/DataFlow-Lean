import Mathlib

open scoped BigOperators

namespace SingularSpectralConnection

/-- The real outer product x yᵀ. -/
def outer {m n : ℕ} (x : Fin m → ℝ) (y : Fin n → ℝ) :
    Matrix (Fin m) (Fin n) ℝ :=
  fun a b => x a * y b

/-- Orthonormality expressed using the real Euclidean inner product. -/
def OrthonormalFamily {d r : ℕ} (w : Fin r → Fin d → ℝ) : Prop :=
  ∀ i j : Fin r,
    (∑ a : Fin d, w i a * w j a : ℝ) =
      if i = j then (1 : ℝ) else (0 : ℝ)

/-- A nonzero eigenvector with the specified real eigenvalue. -/
def IsEigenvector {d : ℕ} (B : Matrix (Fin d) (Fin d) ℝ)
    (coeff : ℝ) (x : Fin d → ℝ) : Prop :=
  x ≠ (0 : Fin d → ℝ) ∧ B.mulVec x = coeff • x

/-- A real eigenvalue, witnessed by a nonzero real eigenvector. -/
def IsEigenvalue {d : ℕ} (B : Matrix (Fin d) (Fin d) ℝ)
    (coeff : ℝ) : Prop :=
  ∃ x : Fin d → ℝ, IsEigenvector B coeff x

/-- Data for a reduced real singular value decomposition of A. -/
def ReducedSVD {m n r : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (s : Fin r → ℝ) (u : Fin r → Fin m → ℝ)
    (v : Fin r → Fin n → ℝ) : Prop :=
  (∀ i : Fin r, (0 : ℝ) < s i) ∧
  OrthonormalFamily u ∧
  OrthonormalFamily v ∧
  A = (∑ i : Fin r, (s i) • outer (u i) (v i) :
    Matrix (Fin m) (Fin n) ℝ)

/-- The Gram-matrix spectral decompositions and the corresponding
singular-value/eigenvalue square-root identities. -/
theorem spectral_connection_of_reducedSVD
    {m n r : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (s : Fin r → ℝ)
    (u : Fin r → Fin m → ℝ)
    (v : Fin r → Fin n → ℝ)
    (hSVD : ReducedSVD A s u v) :
    (A * A.transpose =
      (∑ i : Fin r, ((s i) ^ 2) • outer (u i) (u i) :
        Matrix (Fin m) (Fin m) ℝ)) ∧
    (A.transpose * A =
      (∑ i : Fin r, ((s i) ^ 2) • outer (v i) (v i) :
        Matrix (Fin n) (Fin n) ℝ)) ∧
    (∃ coeffLeft coeffRight : Fin r → ℝ,
      ∀ i : Fin r,
        coeffLeft i = (s i) ^ 2 ∧
        coeffRight i = (s i) ^ 2 ∧
        IsEigenvector (A * A.transpose) (coeffLeft i) (u i) ∧
        IsEigenvector (A.transpose * A) (coeffRight i) (v i) ∧
        IsEigenvalue (A * A.transpose) (coeffLeft i) ∧
        IsEigenvalue (A.transpose * A) (coeffRight i) ∧
        s i = Real.sqrt (coeffLeft i) ∧
        s i = Real.sqrt (coeffRight i)) := by sorry

end SingularSpectralConnection
