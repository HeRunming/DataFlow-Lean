import Mathlib

open MeasureTheory
open scoped BigOperators

noncomputable section

namespace SphereUniformity

/-- The cost of a countable cover, expressed through finite partial sums. -/
def coverCost (k : ℕ) (I : Set ℕ) (d : ℕ → ℝ) : ENNReal :=
  ⨆ (J : Finset ℕ) (_hJ : ∀ i : ℕ, i ∈ J → i ∈ I),
    (∑ i ∈ J, ((ENNReal.ofReal (d i)) ^ k : ENNReal) : ENNReal)

/-- Hausdorff measure defined by countable diameter-bounded covers.
The conventional dimension-dependent normalization is omitted; it cancels
in every relative-area ratio used below. -/
def hausdorffArea {V : Type*} [MetricSpace V]
    (k : ℕ) (E : Set V) : ENNReal :=
  ⨆ (δ : ℝ) (_hδ : (0 : ℝ) < δ),
    ⨅ (I : Set ℕ) (U : ℕ → Set V) (d : ℕ → ℝ)
      (_hcover : ∀ x : V, x ∈ E → ∃ i : ℕ, i ∈ I ∧ x ∈ U i)
      (_hbound : ∀ i : ℕ, i ∈ I →
        (0 : ℝ) ≤ d i ∧ d i ≤ δ ∧
          ∀ x : V, x ∈ U i → ∀ y : V, y ∈ U i → dist x y ≤ d i),
      coverCost k I d

/-- The source's relative surface area uses dimension n - 1. -/
def surfaceArea {n : ℕ}
    (E : Set (EuclideanSpace ℝ (Fin n))) : ENNReal :=
  hausdorffArea (n - 1) E

/-- Uniform distribution means equality with relative surface area for every
Borel subset of a positive-dimensional, positive-radius sphere of finite,
nonzero surface area. -/
def UniformlyDistributedOnSphere
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (hn : 0 < n)
    (X : Ω → EuclideanSpace ℝ (Fin n))
    (c : EuclideanSpace ℝ (Fin n)) (r : ℝ)
    (hr : (0 : ℝ) < r)
    (hfinite : surfaceArea (Metric.sphere c r) ≠ (⊤ : ENNReal))
    (hne : surfaceArea (Metric.sphere c r) ≠ (0 : ENNReal)) : Prop :=
  Measurable X ∧
    ∀ E : Set (EuclideanSpace ℝ (Fin n)),
      MeasurableSet E → E ⊆ Metric.sphere c r →
        P (X ⁻¹' E) = surfaceArea E / surfaceArea (Metric.sphere c r)

/-- The defining characterization of uniform distribution on a sphere. -/
theorem uniformlyDistributedOnSphere_iff
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (hn : 0 < n)
    (X : Ω → EuclideanSpace ℝ (Fin n))
    (hX : Measurable X)
    (c : EuclideanSpace ℝ (Fin n)) (r : ℝ)
    (hr : (0 : ℝ) < r)
    (hfinite : surfaceArea (Metric.sphere c r) ≠ (⊤ : ENNReal))
    (hne : surfaceArea (Metric.sphere c r) ≠ (0 : ENNReal)) :
    UniformlyDistributedOnSphere P hn X c r hr hfinite hne ↔
      ∀ E : Set (EuclideanSpace ℝ (Fin n)),
        MeasurableSet E → E ⊆ Metric.sphere c r →
          P (X ⁻¹' E) = surfaceArea E / surfaceArea (Metric.sphere c r) := by
  sorry

end SphereUniformity
