import Mathlib

open MeasureTheory

namespace RotationInvariantDistributions

/-- The Euclidean inner product, not the product-space supremum norm. -/
def euclideanInner {n : ℕ} (x y : Fin n → ℝ) : ℝ :=
  (∑ i : Fin n, x i * y i : ℝ)

/-- The unit sphere in Euclidean coordinates. -/
def unitSphere (n : ℕ) : Set (Fin n → ℝ) :=
  {x : Fin n → ℝ | euclideanInner x x = (1 : ℝ)}

/-- Invariance under all orthogonal transformations, expressed on measurable sets. -/
def IsRotationInvariant {n : ℕ} (μ : Measure (Fin n → ℝ)) : Prop :=
  ∀ (T : (Fin n → ℝ) → (Fin n → ℝ)),
    Function.Bijective T →
    (∀ (x y : Fin n → ℝ),
      euclideanInner (T x) (T y) = euclideanInner x y) →
    ∀ (s : Set (Fin n → ℝ)), MeasurableSet s →
      μ (T ⁻¹' s) = μ s

/-- Characterization of a uniform sphere law as an orthogonally invariant
probability measure concentrated on the Euclidean unit sphere. -/
def IsUniformOnUnitSphere {n : ℕ} (μ : Measure (Fin n → ℝ)) : Prop :=
  IsProbabilityMeasure μ ∧
    IsRotationInvariant μ ∧
    μ (unitSphere n) = (1 : ENNReal)

/-- Substitution schema for a conclusion that requires only rotation invariance
and the probability-measure condition. -/
theorem any_rotation_invariant_distribution_can_replace_normal
    {n : ℕ}
    {P : Measure (Fin n → ℝ) → Prop}
    (hP : ∀ (μ : Measure (Fin n → ℝ)),
      IsProbabilityMeasure μ → IsRotationInvariant μ → P μ)
    (μ : Measure (Fin n → ℝ))
    [IsProbabilityMeasure μ]
    (hμ : IsRotationInvariant μ) :
    P μ := by sorry

/-- In positive dimension, the uniform sphere distribution supplies an example. -/
theorem uniform_distribution_on_sphere_exists
    (n : ℕ)
    (hn : 0 < n) :
    ∃ (μ : Measure (Fin n → ℝ)), IsUniformOnUnitSphere μ := by sorry

end RotationInvariantDistributions
