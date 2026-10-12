import Mathlib

open MeasureTheory
open scoped BigOperators

namespace PCA

abbrev Vector (n : ℕ) := Fin n → ℝ

-- Explicit Euclidean geometry, not the Pi-space norm.
def dot {n : ℕ} (x y : Vector n) : ℝ :=
  (∑ i : Fin n, x i * y i : ℝ)

def squaredEuclideanNorm {n : ℕ} (x : Vector n) : ℝ :=
  (∑ i : Fin n, (x i) ^ (2 : ℕ) : ℝ)

noncomputable def scalarVariance
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → ℝ) : ℝ :=
  ∫ ω, (f ω - (∫ η, f η ∂μ)) ^ (2 : ℕ) ∂μ

noncomputable def meanZeroCovariance
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) (X : Ω → Vector n) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => ∫ ω, X ω i * X ω j ∂μ

def IsEigenvector {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) (v : Vector n) : Prop :=
  v ≠ 0 ∧
    ∀ j : Fin n, (∑ l : Fin n, C j l * v l : ℝ) = c * v j

-- Records the complete eigenvalue list with multiplicities, without
-- imposing normalization on the source's specified eigenvectors.
def HasEigenvalueList {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (coeff : Fin n → ℝ) : Prop :=
  ∃ w : Fin n → Vector n,
    (∀ i j : Fin n,
      dot (w i) (w j) = (if i = j then (1 : ℝ) else (0 : ℝ))) ∧
    (∀ i : Fin n, IsEigenvector C (coeff i) (w i))

structure Data
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (n : ℕ) where
  probability : IsProbabilityMeasure μ
  X : Ω → Vector n
  measurable_coordinate : ∀ i : Fin n, Measurable (fun ω => X ω i)
  integrable_coordinate : ∀ i : Fin n, Integrable (fun ω => X ω i) μ
  finite_second_moment :
    ∀ i : Fin n, Integrable (fun ω => (X ω i) ^ (2 : ℕ)) μ
  mean_zero : ∀ i : Fin n, (∫ ω, X ω i ∂μ) = (0 : ℝ)
  coeff : Fin n → ℝ
  v : Fin n → Vector n
  decreasing_eigenvalues :
    ∀ i j : Fin n, i ≤ j → coeff j ≤ coeff i
  full_eigenvalue_list : HasEigenvalueList (meanZeroCovariance μ X) coeff
  specified_eigenvectors :
    ∀ i : Fin n, IsEigenvector (meanZeroCovariance μ X) (coeff i) (v i)

def partialSum {n : ℕ} (coeff : Fin n → ℝ) (k : ℕ) : ℝ :=
  (∑ i : Fin n, if i.val < k then coeff i else (0 : ℝ) : ℝ)

def leadingSpan {n : ℕ} (v : Fin n → Vector n) (k : ℕ) :
    Submodule ℝ (Vector n) :=
  Submodule.span ℝ
    {x : Vector n | ∃ i : Fin n, i.val < k ∧ x = v i}

def IsOrthogonalProjection {n : ℕ}
    (P : Vector n →ₗ[ℝ] Vector n) : Prop :=
  (∀ x : Vector n, P (P x) = P x) ∧
  (∀ x y : Vector n, dot (P x) y = dot x (P y))

def IsLeadingOrthogonalProjection {n : ℕ}
    (v : Fin n → Vector n) (k : ℕ)
    (Pk : Vector n →ₗ[ℝ] Vector n) : Prop :=
  IsOrthogonalProjection Pk ∧
    LinearMap.range Pk = leadingSpan v k

def IsRankKOrthogonalProjection {n : ℕ}
    (P : Vector n →ₗ[ℝ] Vector n) (k : ℕ) : Prop :=
  IsOrthogonalProjection P ∧
    Module.finrank ℝ (LinearMap.range P) = k

noncomputable def expectedSquaredNorm
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) (Y : Ω → Vector n) : ℝ :=
  ∫ ω, squaredEuclideanNorm (Y ω) ∂μ

-- Part (a): the literal source assertion, without silently normalizing v.
theorem leading_projection_variance
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (n : ℕ) (D : Data μ n)
    (k : ℕ) (hk : k ≤ n)
    (Pk : Vector n →ₗ[ℝ] Vector n)
    (hPk : IsLeadingOrthogonalProjection D.v k Pk) :
    expectedSquaredNorm μ (fun ω => Pk (D.X ω)) =
      (∑ i : Fin n,
        if i.val < k then
          scalarVariance μ (fun ω => dot (D.X ω) (D.v i))
        else (0 : ℝ) : ℝ) ∧
    (∑ i : Fin n,
        if i.val < k then
          scalarVariance μ (fun ω => dot (D.X ω) (D.v i))
        else (0 : ℝ) : ℝ) = partialSum D.coeff k := by sorry

-- Part (b), with precisely the same shared data and leading projection.
theorem leading_projection_maximizes_variance
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (n : ℕ) (D : Data μ n)
    (k : ℕ) (hk : k ≤ n)
    (Pk : Vector n →ₗ[ℝ] Vector n)
    (hPk : IsLeadingOrthogonalProjection D.v k Pk)
    (P : Vector n →ₗ[ℝ] Vector n)
    (hP : IsRankKOrthogonalProjection P k) :
    expectedSquaredNorm μ (fun ω => P (D.X ω)) ≤
      expectedSquaredNorm μ (fun ω => Pk (D.X ω)) := by sorry

-- Identifies total variance with s_n.
theorem total_variance_eq_eigenvalue_sum
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (n : ℕ) (D : Data μ n) :
    expectedSquaredNorm μ D.X = partialSum D.coeff n := by sorry

-- Only the fraction interpretation requires positive total variance.
theorem explained_variance_fraction
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (n : ℕ) (D : Data μ n)
    (k : ℕ) (hk : k ≤ n)
    (Pk : Vector n →ₗ[ℝ] Vector n)
    (hPk : IsLeadingOrthogonalProjection D.v k Pk)
    (hpositive : (0 : ℝ) < partialSum D.coeff n) :
    expectedSquaredNorm μ (fun ω => Pk (D.X ω)) /
        expectedSquaredNorm μ D.X =
      partialSum D.coeff k / partialSum D.coeff n := by sorry

end PCA
