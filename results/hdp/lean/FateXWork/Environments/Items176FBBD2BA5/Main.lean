import Mathlib

open scoped BigOperators

namespace PoissonLimitTheorem

noncomputable section

/-- The epsilon definition of convergence of a real sequence. -/
def RealSequenceConverges (a : ℕ → ℝ) (b : ℝ) : Prop :=
  ∀ ε : ℝ, (0 : ℝ) < ε →
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → |a n - b| < ε

/-- Row n represents the source row N = n + 1. -/
def rowSum {Ω : Type*} (X : (n : ℕ) → Fin (n + 1) → Ω → ℕ)
    (n : ℕ) (ω : Ω) : ℕ :=
  (∑ i : Fin (n + 1), X n i ω : ℕ)

/-- Mutual independence of the entire triangular family, including across rows. -/
def IndependentFamily {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω)
    (X : (n : ℕ) → Fin (n + 1) → Ω → ℕ) : Prop :=
  ∀ (s : Finset (Σ n : ℕ, Fin (n + 1)))
      (A : (Σ n : ℕ, Fin (n + 1)) → Set ℕ),
    μ {ω : Ω | ∀ j ∈ s, X j.1 j.2 ω ∈ A j} =
      (∏ j ∈ s, μ {ω : Ω | X j.1 j.2 ω ∈ A j} : ENNReal)

/-- The Bernoulli mass function, specifying the law at every natural number. -/
def HasBernoulliLaw {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) (Y : Ω → ℕ) (p : ℝ) : Prop :=
  ∀ k : ℕ,
    μ {ω : Ω | Y ω = k} =
      ENNReal.ofReal
        (if k = (0 : ℕ) then (1 : ℝ) - p
         else if k = (1 : ℕ) then p else (0 : ℝ))

/-- The finite discrete expectation of a row sum supported almost surely
on the natural numbers from 0 through n + 1. -/
def rowExpectation {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω)
    (X : (n : ℕ) → Fin (n + 1) → Ω → ℕ) (n : ℕ) : ℝ :=
  (∑ k ∈ Finset.range (n + 2),
    (k : ℝ) * (μ {ω : Ω | rowSum X n ω = k}).toReal : ℝ)

/-- The Poisson mass function, allowing the parameter coeff = 0. -/
def poissonMass (coeff : ℝ) (k : ℕ) : ℝ :=
  Real.exp (-coeff) * coeff ^ k / (Nat.factorial k : ℝ)

/-- For natural-valued laws and a nonnegative finite parameter, convergence
of all point masses to these Poisson masses characterizes convergence
in distribution to the Poisson law. -/
def ConvergesInDistributionToPoisson {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) (S : ℕ → Ω → ℕ)
    (coeff : ℝ) : Prop :=
  ∀ k : ℕ,
    RealSequenceConverges
      (fun n : ℕ => (μ {ω : Ω | S n ω = k}).toReal)
      (poissonMass coeff k)

/-- Theorem 1.7.6: Poisson limit theorem. -/
theorem poisson_limit
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (X : (n : ℕ) → Fin (n + 1) → Ω → ℕ)
    (p : (n : ℕ) → Fin (n + 1) → ℝ)
    (coeff : ℝ)
    (hcoeff : (0 : ℝ) ≤ coeff)
    (hp : ∀ (n : ℕ) (i : Fin (n + 1)),
      (0 : ℝ) ≤ p n i ∧ p n i ≤ (1 : ℝ))
    (hmeasurable : ∀ (n : ℕ) (i : Fin (n + 1)), Measurable (X n i))
    (hindependent : IndependentFamily μ X)
    (hbernoulli : ∀ (n : ℕ) (i : Fin (n + 1)),
      HasBernoulliLaw μ (X n i) (p n i))
    (hmax : ∀ ε : ℝ, (0 : ℝ) < ε →
      ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
        ∀ i : Fin (n + 1), p n i < ε)
    (hexpectation : ∀ n : ℕ,
      rowExpectation μ X n = (∑ i : Fin (n + 1), p n i : ℝ))
    (hmean : RealSequenceConverges
      (fun n : ℕ => (∑ i : Fin (n + 1), p n i : ℝ)) coeff) :
    ConvergesInDistributionToPoisson μ (rowSum X) coeff := by sorry

end

end PoissonLimitTheorem
