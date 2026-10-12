import Mathlib

open MeasureTheory

universe u v

theorem deterministic_random_decomposition
    {Ω : Type u} [MeasurableSpace Ω]
    {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (A : Ω → E) (hA : Integrable A μ) :
    ∃ (D R : Ω → E),
      D = (fun _ : Ω => ∫ x : Ω, A x ∂μ) ∧
      A = D + R := by
  refine ⟨(fun _ => ∫ x : Ω, A x ∂μ),
    (fun x => A x - ∫ y : Ω, A y ∂μ), rfl, ?_⟩
  funext x
  simp
