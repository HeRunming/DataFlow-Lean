import Mathlib.MeasureTheory.Measure.Real

open Set
open MeasureTheory

namespace Probability

theorem probability_measure_iUnion_eq_sum
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n : ℕ)
    (E : ℕ → Set Ω)
    (hE : ∀ i ∈ Finset.Icc 1 n, MeasurableSet (E i))
    (hdisj : ∀ i ∈ Finset.Icc 1 n, ∀ j ∈ Finset.Icc 1 n, i ≠ j → Disjoint (E i) (E j)) :
    μ (⋃ i ∈ Finset.Icc 1 n, E i) = ∑ i ∈ Finset.Icc 1 n, (μ (E i) : ENNReal) := by
  classical
  rw [measure_biUnion_finset
    (fun i hi j hj hij => hdisj i hi j hj hij)
    (fun i hi => hE i hi)]

theorem probability_measure_iUnion_le_sum
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n : ℕ)
    (E : ℕ → Set Ω)
    (hE : ∀ i ∈ Finset.Icc 1 n, MeasurableSet (E i))
    (hnotdisj : ¬ (∀ i ∈ Finset.Icc 1 n, ∀ j ∈ Finset.Icc 1 n, i ≠ j → Disjoint (E i) (E j))) :
    μ (⋃ i ∈ Finset.Icc 1 n, E i) ≤ ∑ i ∈ Finset.Icc 1 n, (μ (E i) : ENNReal) := by
  classical
  have _ := hE
  have _ := hnotdisj
  exact measure_biUnion_finset_le (Finset.Icc 1 n) E

end Probability
