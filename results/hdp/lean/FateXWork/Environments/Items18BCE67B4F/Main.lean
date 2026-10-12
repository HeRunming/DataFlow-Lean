import Mathlib

open scoped BigOperators
open MeasureTheory

set_option autoImplicit false

def StudentPair (n : ℕ) :=
  {p : Fin n × Fin n // p.1 < p.2}

def pairOf {n : ℕ} {i j : Fin n} (hij : i < j) : StudentPair n :=
  ⟨(i, j), hij⟩

def IsIndependentAt {Ω : Type*} {n : ℕ}
    (friendship : StudentPair n → Set Ω) (ω : Ω)
    (S : Finset (Fin n)) : Prop :=
  ∀ ⦃i j : Fin n⦄, i ∈ S → j ∈ S → ∀ (hij : i < j),
    ω ∉ friendship (pairOf (n := n) (i := i) (j := j) hij)

def PairEventsMutuallyIndependent {Ω : Type*} {n : ℕ}
    [MeasurableSpace Ω] (μ : Measure Ω)
    (friendship : StudentPair n → Set Ω) : Prop :=
  ∀ s : Finset (StudentPair n),
    μ.real (⋂ p ∈ s, friendship p) =
      (∏ p ∈ s, μ.real (friendship p) : ℝ)

def HasLargeIndependentSet {Ω : Type*} {n : ℕ}
    (friendship : StudentPair n → Set Ω) (ω : Ω) : Prop :=
  ∃ S : Finset (Fin n),
    (2 : ℝ) * Real.logb (2 : ℝ) (n : ℝ) < (S.card : ℝ) ∧
      IsIndependentAt friendship ω S

def NoLargeIndependentSet {Ω : Type*} {n : ℕ}
    (friendship : StudentPair n → Set Ω) : Set Ω :=
  {ω | ¬ HasLargeIndependentSet friendship ω}

theorem highDimensionalProbability_no_large_independent_set
    (n : ℕ) (hn : 7 ≤ n)
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (friendship : StudentPair n → Set Ω)
    (h_measurable : ∀ p : StudentPair n, MeasurableSet (friendship p))
    (h_probability : ∀ p : StudentPair n,
      μ.real (friendship p) = (1 / 2 : ℝ))
    (h_independent : PairEventsMutuallyIndependent μ friendship) :
    μ.real (NoLargeIndependentSet friendship) ≥
      (1 : ℝ) - (1 : ℝ) / (n : ℝ) := by sorry
