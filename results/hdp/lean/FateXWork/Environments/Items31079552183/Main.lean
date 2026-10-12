import Mathlib

open MeasureTheory
open scoped BigOperators

namespace MeanCovarianceSignatures

universe u

abbrev Vec (n : ℕ) := Fin n → ℝ

/-- The source's symmetric positive semidefinite condition. -/
def SymmetricPSD {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  (∀ i j : Fin n, A i j = A j i) ∧
  ∀ v : Vec n,
    (0 : ℝ) ≤
      (∑ i : Fin n,
        (∑ j : Fin n, v i * A i j * v j : ℝ) : ℝ)

/-- A relational specification of the symmetric PSD square root. -/
def IsPSDSquareRoot {n : ℕ}
    (sigma root : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  SymmetricPSD root ∧
  ∀ i j : Fin n,
    (∑ k : Fin n, root i k * root k j : ℝ) = sigma i j

def identityCov (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if i = j then (1 : ℝ) else (0 : ℝ)

/-- Coordinatewise expectation and centered covariance, with finite moments. -/
def HasMeanCov {n : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Vec n) (mu : Vec n)
    (sigma : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  Measurable X ∧
  (∀ i : Fin n, Integrable (fun omega => X omega i) P) ∧
  (∀ i j : Fin n,
    Integrable
      (fun omega => (X omega i - mu i) * (X omega j - mu j)) P) ∧
  (∀ i : Fin n, (∫ omega, X omega i ∂P) = mu i) ∧
  (∀ i j : Fin n,
    (∫ omega, (X omega i - mu i) * (X omega j - mu j) ∂P) =
      sigma i j)

def MeanZeroIsotropic {n : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) (Z : Ω → Vec n) : Prop :=
  HasMeanCov P Z (fun _ : Fin n => (0 : ℝ)) (identityCov n)

/-- The source defines this affine transformation pointwise. -/
def affineImage {n : ℕ} {Ω : Type u}
    (mu : Vec n) (root : Matrix (Fin n) (Fin n) ℝ)
    (Z : Ω → Vec n) : Ω → Vec n :=
  fun omega i =>
    mu i + (∑ j : Fin n, root i j * Z omega j : ℝ)

/-- Part (a). -/
theorem part_a
    {n : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (mu : Vec n) (sigma root : Matrix (Fin n) (Fin n) ℝ)
    (hsigma : SymmetricPSD sigma)
    (hroot : IsPSDSquareRoot sigma root)
    (Z : Ω → Vec n) (hZ : MeanZeroIsotropic P Z) :
    HasMeanCov P (affineImage mu root Z) mu sigma := by sorry

/-- Part (b), retaining the source's requested same-space conclusion.
This assertion is not valid in full generality for singular covariance. -/
theorem part_b
    {n : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (mu : Vec n) (sigma root : Matrix (Fin n) (Fin n) ℝ)
    (hsigma : SymmetricPSD sigma)
    (hroot : IsPSDSquareRoot sigma root)
    (X : Ω → Vec n) (hX : HasMeanCov P X mu sigma) :
    ∃ Z : Ω → Vec n,
      MeanZeroIsotropic P Z ∧
      (∀ᵐ omega ∂P, X omega = affineImage mu root Z omega) := by sorry

end MeanCovarianceSignatures
