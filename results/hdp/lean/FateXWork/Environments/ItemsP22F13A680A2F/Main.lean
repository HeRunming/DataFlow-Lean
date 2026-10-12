import Mathlib

open MeasureTheory
open ProbabilityTheory

theorem law_of_total_probability
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (E : Set Ω) (F : ℕ → Set Ω)
    (hE : MeasurableSet E)
    (hF : ∀ i : ℕ, MeasurableSet (F i))
    (hdisjoint : Set.PairwiseDisjoint Set.univ F)
    (hcover : (⋃ i : ℕ, F i) = Set.univ)
    (hpositive : ∀ i : ℕ, 0 < μ (F i)) :
    (μ E).toReal =
      (∑' i : ℕ,
        ((((μ (E ∩ F i)) / (μ (F i))).toReal) * (μ (F i)).toReal) : ℝ) := by
  have hd' : Pairwise (fun i j => Disjoint (E ∩ F i) (E ∩ F j)) := by
    intro i j hij
    exact (hdisjoint (Set.mem_univ i) (Set.mem_univ j) hij).mono Set.inter_subset_right Set.inter_subset_right
  have hu : (⋃ i, E ∩ F i) = E := by
    rw [← Set.inter_iUnion, hcover, Set.inter_univ]
  have hm : μ E = ∑' i, μ (E ∩ F i) := by
    rw [← measure_iUnion hd' (fun i => hE.inter (hF i)), hu]
  rw [hm, ENNReal.tsum_toReal_eq]
  · apply tsum_congr
    intro i
    rw [ENNReal.toReal_div]
    exact (div_mul_cancel₀ _ (ENNReal.toReal_ne_zero.mpr ⟨ne_of_gt (hpositive i), measure_ne_top μ (F i)⟩)).symm
  · intro i
    exact measure_ne_top μ _
