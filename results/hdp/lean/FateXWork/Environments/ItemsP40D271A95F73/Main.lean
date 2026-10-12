import Mathlib

universe u v w z

namespace IndependentCopiesFormalization

/-- A measurable family of independent random variables with the law of `X`. -/
def IndependentCopies
    {Ω : Type u} {Ω' : Type v} {E : Type w} {ι : Type z}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace E]
    (μ : MeasureTheory.Measure Ω) (ν : MeasureTheory.Measure Ω')
    [MeasureTheory.IsProbabilityMeasure μ]
    [MeasureTheory.IsProbabilityMeasure ν]
    (X : Ω → E) (Y : ι → Ω' → E) : Prop :=
  Measurable X ∧
  (∀ i : ι, Measurable (Y i)) ∧
  ProbabilityTheory.iIndepFun Y ν ∧
  (∀ i : ι, MeasureTheory.Measure.map (Y i) ν =
    MeasureTheory.Measure.map X μ)

/-- Independent copies are independent random variables having the law of `X`. -/
theorem independentCopies_iff
    {Ω : Type u} {Ω' : Type v} {E : Type w} {ι : Type z}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace E]
    (μ : MeasureTheory.Measure Ω) (ν : MeasureTheory.Measure Ω')
    [MeasureTheory.IsProbabilityMeasure μ]
    [MeasureTheory.IsProbabilityMeasure ν]
    (X : Ω → E) (Y : ι → Ω' → E) :
    IndependentCopies μ ν X Y ↔
      Measurable X ∧
      (∀ i : ι, Measurable (Y i)) ∧
      ProbabilityTheory.iIndepFun Y ν ∧
      (∀ i : ι, MeasureTheory.Measure.map (Y i) ν =
        MeasureTheory.Measure.map X μ) := by
  set_option maxHeartbeats 5000 in
    first | (rfl; done) | (assumption; done) | (simp; done) | (norm_num; done) | (omega; done) | (linarith; done) | (ring; done) | (simp_all [IndependentCopies]; done)

end IndependentCopiesFormalization
