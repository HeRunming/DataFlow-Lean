import Mathlib

open MeasureTheory
open scoped BigOperators Topology

noncomputable section

namespace BernoulliBinomialExample

/-- The Bernoulli law, expressed directly by its two atom probabilities. -/
def HasBernoulliLaw {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Y : Ω → ℝ) (p : ℝ) : Prop :=
  Measurable Y ∧
  μ {ω : Ω | Y ω = (1 : ℝ)} = ENNReal.ofReal p ∧
  μ {ω : Ω | Y ω = (0 : ℝ)} = ENNReal.ofReal ((1 : ℝ) - p) ∧
  μ {ω : Ω | Y ω ≠ (0 : ℝ) ∧ Y ω ≠ (1 : ℝ)} = (0 : ENNReal)

/-- Mutual independence, not merely pairwise independence. -/
def IndependentSequence {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : ℕ → Ω → ℝ) : Prop :=
  ∀ (I : Finset ℕ) (A : ℕ → Set ℝ),
    (∀ i ∈ I, MeasurableSet (A i)) →
      μ {ω : Ω | ∀ i ∈ I, X i ω ∈ A i} =
        (∏ i ∈ I, μ {ω : Ω | X i ω ∈ A i} : ENNReal)

/-- Ordinary real expectation; finiteness is asserted in the moment theorem. -/
def sourceMean {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Y : Ω → ℝ) : ℝ :=
  ∫ ω : Ω, Y ω ∂μ

/-- Variance as the expectation of the squared centered random variable. -/
def sourceVariance {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Y : Ω → ℝ) : ℝ :=
  ∫ ω : Ω, (Y ω - sourceMean μ Y) ^ (2 : ℕ) ∂μ

/-- The source's sum X₁ + ⋯ + X_N. The unused coordinate X₀ is unrestricted. -/
def partialSum {Ω : Type*} (X : ℕ → Ω → ℝ)
    (N : ℕ) (ω : Ω) : ℝ :=
  (∑ i : Fin N, X (i.val + 1) ω : ℝ)

/-- The binomial law, specified by its finite support and atom probabilities. -/
def HasBinomialLaw {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Y : Ω → ℝ) (N : ℕ) (p : ℝ) : Prop :=
  Measurable Y ∧
  μ {ω : Ω | ¬ ∃ k : Fin (N + 1), Y ω = (k.val : ℝ)} =
    (0 : ENNReal) ∧
  ∀ k : Fin (N + 1),
    μ {ω : Ω | Y ω = (k.val : ℝ)} =
      ENNReal.ofReal
        ((N.choose k.val : ℝ) * p ^ k.val *
          ((1 : ℝ) - p) ^ (N - k.val))

/-- The normalization in equation (1.25). -/
def normalizedSum {Ω : Type*} (X : ℕ → Ω → ℝ)
    (p : ℝ) (N : ℕ) (ω : Ω) : ℝ :=
  (partialSum X N ω - (N : ℝ) * p) /
    Real.sqrt ((N : ℝ) * p * ((1 : ℝ) - p))

/-- The upper tail of the standard normal law, as in Theorem 1.7.3. -/
def standardNormalTail (t : ℝ) : ℝ :=
  ((1 : ℝ) / Real.sqrt ((2 : ℝ) * Real.pi)) *
    (∫ x : ℝ in Set.Ioi t,
      Real.exp (-(x ^ (2 : ℕ)) / (2 : ℝ)))

/-- Convergence to N(0,1), using the source's pointwise upper-tail formulation. -/
def ConvergesToStandardNormal {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Z : ℕ → Ω → ℝ) : Prop :=
  (∀ N : ℕ, Measurable (Z N)) ∧
  ∀ t : ℝ,
    Filter.Tendsto
      (fun N : ℕ => (μ {ω : Ω | t < Z N ω}).toReal)
      Filter.atTop (nhds (standardNormalTail t))

 theorem bernoulli_moments
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : Ω → ℝ) (p : ℝ)
    (hp_pos : (0 : ℝ) < p) (hp_lt_one : p < (1 : ℝ))
    (hY : HasBernoulliLaw μ Y p) :
    Integrable Y μ ∧
    Integrable (fun ω : Ω => (Y ω) ^ (2 : ℕ)) μ ∧
    Integrable
      (fun ω : Ω => (Y ω - sourceMean μ Y) ^ (2 : ℕ)) μ ∧
    sourceMean μ Y = p ∧
    sourceVariance μ Y = p * ((1 : ℝ) - p) := by sorry

 theorem independent_bernoulli_sum_has_binomial_law
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (p : ℝ)
    (hp_pos : (0 : ℝ) < p) (hp_lt_one : p < (1 : ℝ))
    (hX : ∀ i : ℕ, HasBernoulliLaw μ (X (i + 1)) p)
    (hind : IndependentSequence μ (fun i : ℕ => X (i + 1)))
    (N : ℕ) :
    HasBinomialLaw μ (partialSum X N) N p := by sorry

 theorem de_moivre_laplace
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (p : ℝ)
    (hp_pos : (0 : ℝ) < p) (hp_lt_one : p < (1 : ℝ))
    (hX : ∀ i : ℕ, HasBernoulliLaw μ (X (i + 1)) p)
    (hind : IndependentSequence μ (fun i : ℕ => X (i + 1))) :
    ConvergesToStandardNormal μ (normalizedSum X p) := by sorry

end BernoulliBinomialExample
