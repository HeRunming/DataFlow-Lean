import Mathlib

open MeasureTheory Filter
open scoped BigOperators Topology

noncomputable section

namespace LindebergLevy

/-- Independence expressed through all finite families of measurable events. -/
def IndependentSequence {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → ℝ) : Prop :=
  ∀ (s : Finset ℕ) (A : ℕ → Set ℝ),
    (∀ i : ℕ, MeasurableSet (A i)) →
      P {ω : Ω | ∀ i ∈ s, X i ω ∈ A i} =
        s.prod (fun i : ℕ => P {ω : Ω | X i ω ∈ A i})

/-- Identical distributions, expressed on measurable subsets of the real line. -/
def IdenticallyDistributed {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → ℝ) : Prop :=
  ∀ (i j : ℕ) (A : Set ℝ), MeasurableSet A →
    P {ω : Ω | X i ω ∈ A} = P {ω : Ω | X j ω ∈ A}

def expectation {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Y : Ω → ℝ) : ℝ :=
  ∫ ω : Ω, Y ω ∂P

/-- The ordinary centered second moment. -/
def variance {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Y : Ω → ℝ) : ℝ :=
  ∫ ω : Ω, (Y ω - expectation P Y) ^ (2 : ℕ) ∂P

/-- Lean's X 0 denotes the source's X₁. -/
def partialSum {Ω : Type*} (X : ℕ → Ω → ℝ)
    (N : ℕ) (ω : Ω) : ℝ :=
  ((∑ i : Fin N, X i.val ω) : ℝ)

def normalizedSum {Ω : Type*} (X : ℕ → Ω → ℝ)
    (μ σ : ℝ) (N : ℕ) (ω : Ω) : ℝ :=
  ((∑ i : Fin N, (X i.val ω - μ)) : ℝ) /
    (σ * Real.sqrt (N : ℝ))

/-- The standard normal upper-tail probability, written as the source integral. -/
def standardNormalTail (t : ℝ) : ℝ :=
  ((1 : ℝ) / Real.sqrt ((2 : ℝ) * Real.pi)) *
    (∫ x : ℝ, Real.exp (-(x ^ (2 : ℕ)) / (2 : ℝ))
      ∂((volume : Measure ℝ).restrict (Set.Ioi t)))

/-- The standard normal cumulative distribution function. -/
def standardNormalCDF (t : ℝ) : ℝ :=
  ((1 : ℝ) / Real.sqrt ((2 : ℝ) * Real.pi)) *
    (∫ x : ℝ, Real.exp (-(x ^ (2 : ℕ)) / (2 : ℝ))
      ∂((volume : Measure ℝ).restrict (Set.Iic t)))

/-- Theorem 1.7.3, including the normalization and its pointwise CDF/tail formulation. -/
theorem lindeberg_levy_central_limit
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (μ σ : ℝ)
    (hσ : (0 : ℝ) < σ)
    (h_measurable : ∀ i : ℕ, Measurable (X i))
    (h_integrable : ∀ i : ℕ, Integrable (X i) P)
    (h_second_moment : ∀ i : ℕ,
      Integrable (fun ω : Ω => (X i ω - μ) ^ (2 : ℕ)) P)
    (h_independent : IndependentSequence P X)
    (h_identical : IdenticallyDistributed P X)
    (h_mean : ∀ i : ℕ, expectation P (X i) = μ)
    (h_variance : ∀ i : ℕ, variance P (X i) = σ ^ (2 : ℕ)) :
    (∀ N : ℕ, 0 < N →
      Integrable (partialSum X N) P ∧
      Integrable (fun ω : Ω =>
        (partialSum X N ω - expectation P (partialSum X N)) ^ (2 : ℕ)) P ∧
      Integrable (normalizedSum X μ σ N) P ∧
      Integrable (fun ω : Ω =>
        (normalizedSum X μ σ N ω) ^ (2 : ℕ)) P ∧
      (∀ ω : Ω,
        normalizedSum X μ σ N ω =
          (partialSum X N ω - expectation P (partialSum X N)) /
            Real.sqrt (variance P (partialSum X N))) ∧
      expectation P (normalizedSum X μ σ N) = (0 : ℝ) ∧
      variance P (normalizedSum X μ σ N) = (1 : ℝ)) ∧
    (∀ t : ℝ,
      Tendsto
        (fun N : ℕ =>
          (P {ω : Ω | normalizedSum X μ σ N ω ≤ t}).toReal)
        atTop (nhds (standardNormalCDF t))) ∧
    (∀ t : ℝ,
      Tendsto
        (fun N : ℕ =>
          (P {ω : Ω | t < normalizedSum X μ σ N ω}).toReal)
        atTop (nhds (standardNormalTail t))) := by sorry

end LindebergLevy
