import Mathlib.Probability.CDF
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.MeasureTheory.Measure.Real

open Set
open MeasureTheory
open ProbabilityTheory

theorem probability_gt_eq_one_sub_cdf
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : Measurable X) (t : ℝ) :
    μ.real {ω : Ω | X ω > t} =
      1 - (ProbabilityTheory.cdf (Measure.map X μ) t : ℝ) := by
  haveI : IsProbabilityMeasure (Measure.map X μ) := Measure.isProbabilityMeasure_map hX.aemeasurable
  rw [cdf_eq_real]
  simp only [Measure.real, Measure.map_apply hX measurableSet_Iic]
  have hs : MeasurableSet {ω : Ω | X ω ≤ t} := measurableSet_Iic.preimage hX
  have he : {ω : Ω | X ω > t} = {ω : Ω | X ω ≤ t}ᶜ := by
    ext ω
    simp
  rw [he, measure_compl hs (measure_ne_top μ _)]
  rw [ENNReal.toReal_sub_of_le (measure_mono (subset_univ _)) (measure_ne_top μ _)]
  simp only [measure_univ, ENNReal.toReal_one]
  rfl
