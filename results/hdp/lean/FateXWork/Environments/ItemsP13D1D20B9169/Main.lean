import Mathlib

open MeasureTheory

theorem probabilistic_method
    {Ω : Type*} {α : Type*}
    [MeasurableSpace Ω] [MeasurableSpace α]
    (μ : Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    (X : Ω → α)
    (hX : Measurable X)
    (useful : α → Prop)
    (huseful : MeasurableSet {ω : Ω | useful (X ω)})
    (hprob : μ {ω : Ω | useful (X ω)} > (0 : ENNReal)) :
    ∃ a : α, useful a := by
  by_contra! h
  have he : {ω : Ω | useful (X ω)} = (∅ : Set Ω) := by
    ext ω
    simp [h (X ω)]
  have : μ (∅ : Set Ω) > (0 : ENNReal) := by
    simp [he] at hprob
  simp at this
