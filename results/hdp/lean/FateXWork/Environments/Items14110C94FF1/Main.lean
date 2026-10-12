import Mathlib

open MeasureTheory

theorem finite_union_probability_le_sum
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n : ℕ)
    (E : Fin n → Set Ω)
    (hE : ∀ i : Fin n, MeasurableSet (E i)) :
    μ (⋃ i : Fin n, E i) ≤ ((∑ i : Fin n, μ (E i)) : ENNReal) := by
  calc
    μ (⋃ i : Fin n, E i) ≤ ∑' i : Fin n, μ (E i) := measure_iUnion_le E
    _ = ∑ i : Fin n, μ (E i) := tsum_fintype _
