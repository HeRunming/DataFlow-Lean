import Mathlib

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace HighDimensionalVariance

/-- The Euclidean dot product on real coordinate vectors. -/
def euclideanInnerProduct {n : ℕ} (x y : Fin n → ℝ) : ℝ :=
  (∑ i : Fin n, (x i * y i : ℝ) : ℝ)

/-- The source's squared Euclidean norm, defined by a sum of squares. -/
def squaredEuclideanNorm {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  (∑ i : Fin n, ((x i) ^ (2 : ℕ) : ℝ) : ℝ)

theorem innerProduct_self_eq_squaredEuclideanNorm
    {n : ℕ} (x : Fin n → ℝ) :
    euclideanInnerProduct x x = squaredEuclideanNorm x := by simp [euclideanInnerProduct, squaredEuclideanNorm, pow_two]

/-- Coordinatewise expectation on the finite-second-moment domain. -/
def vectorExpectation
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → Fin n → ℝ)
    (hX : Measurable X)
    (hX2 : ∀ i : Fin n,
      MemLp (fun ω : Ω => X ω i) (2 : ENNReal) μ) :
    Fin n → ℝ :=
  fun i : Fin n => ∫ ω : Ω, X ω i ∂μ

/-- Variance obtained by interpreting the square as a Euclidean dot product. -/
def innerProductVariance
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → Fin n → ℝ)
    (hX : Measurable X)
    (hX2 : ∀ i : Fin n,
      MemLp (fun ω : Ω => X ω i) (2 : ENNReal) μ) : ℝ :=
  ∫ ω : Ω, squaredEuclideanNorm
    (fun i : Fin n => X ω i - vectorExpectation μ X hX hX2 i) ∂μ

/-- The expectation of the centered outer product, taken entrywise. -/
def covarianceMatrix
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → Fin n → ℝ)
    (hX : Measurable X)
    (hX2 : ∀ i : Fin n,
      MemLp (fun ω : Ω => X ω i) (2 : ENNReal) μ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun (i : Fin n) (j : Fin n) =>
    ∫ ω : Ω,
      Matrix.vecMulVec
        (fun k : Fin n => X ω k - vectorExpectation μ X hX hX2 k)
        (fun k : Fin n => X ω k - vectorExpectation μ X hX hX2 k)
        i j ∂μ

theorem covarianceMatrix_entry
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → Fin n → ℝ)
    (hX : Measurable X)
    (hX2 : ∀ k : Fin n,
      MemLp (fun ω : Ω => X ω k) (2 : ENNReal) μ)
    (i j : Fin n) :
    covarianceMatrix μ X hX hX2 i j =
      ProbabilityTheory.covariance
        (fun ω : Ω => X ω i) (fun ω : Ω => X ω j) μ := by
  rfl

end HighDimensionalVariance
