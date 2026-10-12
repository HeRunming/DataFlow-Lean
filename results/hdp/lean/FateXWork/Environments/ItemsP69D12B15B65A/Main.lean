import Mathlib

open MeasureTheory

universe u

namespace SourceCovariance

noncomputable def meanVector
    {Ω : Type u} [MeasurableSpace Ω] {n : ℕ}
    (ℙ : Measure Ω) (X : Ω → Fin n → ℝ) : Fin n → ℝ :=
  fun (i : Fin n) => ∫ ω, X ω i ∂ℙ

def outerProduct
    {n : ℕ} (v w : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun (i j : Fin n) => v i * w j

noncomputable def expectedOuterProduct
    {Ω : Type u} [MeasurableSpace Ω] {n : ℕ}
    (ℙ : Measure Ω) (X : Ω → Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun (i j : Fin n) => ∫ ω, X ω i * X ω j ∂ℙ

noncomputable def covarianceMatrix
    {Ω : Type u} [MeasurableSpace Ω] {n : ℕ}
    (ℙ : Measure Ω) (X : Ω → Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun (i j : Fin n) =>
    ∫ ω, (X ω i - meanVector ℙ X i) *
      (X ω j - meanVector ℙ X j) ∂ℙ

theorem covarianceMatrix_eq_sub
    {Ω : Type u} [MeasurableSpace Ω] {n : ℕ}
    (ℙ : Measure Ω) [IsProbabilityMeasure ℙ]
    (X : Ω → Fin n → ℝ)
    (hXmeas : Measurable X)
    (hX : ∀ (i : Fin n), Integrable (fun ω : Ω => X ω i) ℙ)
    (hXX : ∀ (i j : Fin n),
      Integrable (fun ω : Ω => X ω i * X ω j) ℙ) :
    covarianceMatrix ℙ X =
      expectedOuterProduct ℙ X -
        outerProduct (meanVector ℙ X) (meanVector ℙ X) := by sorry

end SourceCovariance
