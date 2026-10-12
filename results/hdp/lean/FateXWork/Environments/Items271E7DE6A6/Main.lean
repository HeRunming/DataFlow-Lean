import Mathlib

open MeasureTheory
open scoped BigOperators ENNReal

namespace BoundedDensitySmallSum

/-- Finite mutual independence, expressed directly using measurable events. -/
def IndependentFamily
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (N : ℕ) (X : Fin N → Ω → ℝ) : Prop :=
  ∀ (s : Finset (Fin N)) (A : Fin N → Set ℝ),
    (∀ i : Fin N, MeasurableSet (A i)) →
      μ {ω : Ω | ∀ i ∈ s, X i ω ∈ A i} =
        (∏ i ∈ s, μ {ω : Ω | X i ω ∈ A i} : ENNReal)

/-- A real-valued density representing the distribution on every measurable set. -/
def HasDensity
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℝ) (f : ℝ → ℝ) : Prop :=
  Measurable f ∧
    (∀ t : ℝ, (0 : ℝ) ≤ f t) ∧
    ∀ B : Set ℝ, MeasurableSet B →
      μ {ω : Ω | X ω ∈ B} =
        ∫⁻ t : ℝ in B, ENNReal.ofReal (f t) ∂volume

 theorem probability_sum_le
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (N : ℕ) (X : Fin N → Ω → ℝ)
    (f : Fin N → ℝ → ℝ) (K : ℝ)
    (h_measurable : ∀ i : Fin N, Measurable (X i))
    (h_nonnegative : ∀ (i : Fin N) (ω : Ω), (0 : ℝ) ≤ X i ω)
    (h_independent : IndependentFamily μ N X)
    (h_density : ∀ i : Fin N, HasDensity μ (X i) (f i))
    (h_bounded : ∀ (i : Fin N) (t : ℝ), f i t ≤ K)
    (ε : ℝ) (hε : (0 : ℝ) < ε) :
    (μ {ω : Ω |
      (∑ i : Fin N, X i ω : ℝ) ≤ ε * (N : ℝ)}).toReal ≤
      (Real.exp (1 : ℝ) * K * ε) ^ N := by sorry

end BoundedDensitySmallSum
