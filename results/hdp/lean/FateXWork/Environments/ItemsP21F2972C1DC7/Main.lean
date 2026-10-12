import Mathlib

open MeasureTheory

/-- The countable law of total probability, with conditional probabilities
characterized without division on null partition cells. -/
theorem total_probability_of_countable_partition
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (E : Set Ω) (F : ℕ → Set Ω)
    (hE : MeasurableSet E)
    (hF : ∀ i : ℕ, MeasurableSet (F i))
    (hpartition : ∀ ω : Ω, ∃! i : ℕ, ω ∈ F i)
    (coeff : ℕ → ENNReal)
    (hcoeff : ∀ i : ℕ, coeff i ≤ (1 : ENNReal))
    (hconditional : ∀ i : ℕ, μ (E ∩ F i) = coeff i * μ (F i)) :
    μ E = ∑' (i : ℕ), (coeff i * μ (F i) : ENNReal) := by
  have hcover : E = ⋃ i, E ∩ F i := by
    ext ω
    constructor
    · intro hω
      obtain ⟨i, hi, _⟩ := hpartition ω
      exact Set.mem_iUnion.2 ⟨i, hω, hi⟩
    · intro hω
      obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hω
      exact hi.1
  have hdisj : Pairwise (Function.onFun Disjoint (fun i => E ∩ F i)) := by
    intro i j hij
    apply Set.disjoint_left.2
    intro ω hi hj
    obtain ⟨k, hk, huniq⟩ := hpartition ω
    exact hij ((huniq i hi.2).trans (huniq j hj.2).symm)
  calc
    μ E = μ (⋃ i, E ∩ F i) := congrArg μ hcover
    _ = ∑' i, μ (E ∩ F i) := measure_iUnion hdisj (fun i => hE.inter (hF i))
    _ = ∑' i, coeff i * μ (F i) := tsum_congr hconditional
