import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

open MeasureTheory

noncomputable def LpRepresentatives
    {Ω : Type u} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [IsProbabilityMeasure μ]
    (p : ℝ) (hp : (1 : ℝ) ≤ p) : Set (Ω → ℝ) :=
  {X | Measurable X ∧ MeasureTheory.eLpNorm X (ENNReal.ofReal p) μ < ⊤}

noncomputable def LpSpace
    {Ω : Type u} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [IsProbabilityMeasure μ]
    (p : ℝ) (hp : (1 : ℝ) ≤ p) : Type _ :=
  MeasureTheory.Lp ℝ (ENNReal.ofReal p) μ

theorem mem_LpRepresentatives_iff
    {Ω : Type u} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [IsProbabilityMeasure μ]
    (p : ℝ) (hp : (1 : ℝ) ≤ p) (X : Ω → ℝ) :
    X ∈ LpRepresentatives μ p hp ↔
      Measurable X ∧ MeasureTheory.eLpNorm X (ENNReal.ofReal p) μ < ⊤ := by
  sorry
