import Mathlib

namespace FateXWork.Environments.Items1135D2C7E94

open scoped BigOperators
open MeasureTheory

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [Nonempty ι]

/-- The pointwise maximum of a nonempty finite family of real-valued functions. -/
def familyMax (X : ι → Ω → ℝ) (ω : Ω) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => X i ω)

/-- Expectation on a finite probability space presented by a probability mass function. -/
def finiteExpectation {α : Type*} [Fintype α] (p : α → ℝ) (Z : α → ℝ) : ℝ :=
  ∑ ω, p ω * Z ω

/-- Probability of an event under a finite probability mass function. -/
noncomputable def finiteEventProb {α : Type*} [Fintype α]
    (p : α → ℝ) (A : Set α) : ℝ :=
  ∑ ω, A.indicator p ω

/-- Mutual independence for a finite family on a finite sample space, expressed
by factorization of finite intersections of inverse images of Borel sets. -/
def FiniteIndependent {α κ : Type*} [Fintype α] [Fintype κ]
    (p : α → ℝ) (X : κ → α → ℝ) : Prop :=
  ∀ (s : Finset κ) (A : κ → Set ℝ),
    (∀ i ∈ s, MeasurableSet (A i)) →
      finiteEventProb p {ω | ∀ i ∈ s, X i ω ∈ A i} =
        ∏ i ∈ s, finiteEventProb p {ω | X i ω ∈ A i}

/-- Source: exercise 1.13(a).

Proof sketch: each `X i` is pointwise bounded by `familyMax X`, giving the lower
bound by monotonicity of the integral. The maximum is bounded by the sum because
all variables are nonnegative; integrate and bound every summand by the largest
expectation. -/
theorem expectation_familyMax_bounds (μ : Measure Ω) (X : ι → Ω → ℝ)
    (hX : ∀ i, Integrable (X i) μ)
    (h_nonneg : ∀ i ω, 0 ≤ X i ω) :
    (∀ i, ∫ ω, X i ω ∂μ ≤ ∫ ω, familyMax X ω ∂μ) ∧
      (∫ ω, familyMax X ω ∂μ) ≤
        (Fintype.card ι : ℝ) *
          Finset.univ.sup' Finset.univ_nonempty (fun i => ∫ ω, X i ω ∂μ) := by
  sorry

/-- Source: exercise 1.13(b), equality in the lower bound.

Proof sketch: take a one-point probability space and let every variable be the
same positive constant. Its maximum is that same constant. -/
theorem lower_bound_is_sharp :
    ∃ (p : Unit → ℝ) (X : ι → Unit → ℝ),
      (∀ ω, 0 ≤ p ω) ∧ (∑ ω, p ω) = 1 ∧
      (∀ i ω, 0 ≤ X i ω) ∧
      Finset.univ.sup' Finset.univ_nonempty
          (fun i => finiteExpectation p (X i)) =
        finiteExpectation p (familyMax X) ∧
      0 < finiteExpectation p (familyMax X) := by
  sorry

/-- Source: exercise 1.13(b), equality in the upper bound.

Proof sketch: use the uniform space on the index set and let `Y i` be the
indicator of outcome `i`. Exactly one variable is one at each outcome, while
each individual expectation is `1 / card ι`. -/
theorem upper_bound_is_sharp :
    ∃ (p : ι → ℝ) (Y : ι → ι → ℝ),
      (∀ ω, 0 ≤ p ω) ∧ (∑ ω, p ω) = 1 ∧
      (∀ i ω, 0 ≤ Y i ω) ∧
      finiteExpectation p (familyMax Y) =
        (Fintype.card ι : ℝ) *
          Finset.univ.sup' Finset.univ_nonempty
            (fun i => finiteExpectation p (Y i)) ∧
      0 < finiteExpectation p (familyMax Y) := by
  sorry

/-- Source: exercise 1.13(c).

Proof sketch: take independent rare Bernoulli variables with success probability
of order `1 / n`. Their maximum indicates at least one success, so its expectation
stays bounded below by an absolute positive constant while each individual
expectation is of order `1 / n`. -/
theorem independent_upper_bound_approximately_sharp :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ+,
      ∃ (p : (Fin n → Bool) → ℝ) (X : Fin n → (Fin n → Bool) → ℝ),
        (∀ ω, 0 ≤ p ω) ∧ (∑ ω, p ω) = 1 ∧
        (∀ i ω, 0 ≤ X i ω) ∧ FiniteIndependent p X ∧
        finiteExpectation p (familyMax X) >
          c * (n : ℝ) *
            Finset.univ.sup' Finset.univ_nonempty
              (fun i => finiteExpectation p (X i)) := by
  sorry

end FateXWork.Environments.Items1135D2C7E94
