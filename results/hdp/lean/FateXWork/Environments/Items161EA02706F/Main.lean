import Mathlib

open MeasureTheory

universe u

theorem nonnegative_random_variable_tail_expectation
    {Ω : Type u} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (X : Ω → ℝ)
    (hX_measurable : Measurable X)
    (hX_nonnegative : ∀ ω : Ω, (0 : ℝ) ≤ X ω) :
    let expectation : ENNReal :=
      ∫⁻ ω : Ω, ENNReal.ofReal (X ω) ∂μ
    let tailIntegral : ENNReal :=
      ∫⁻ t : ℝ in Set.Ioi (0 : ℝ),
        μ {ω : Ω | t < X ω}
        ∂(@MeasureTheory.volume ℝ Real.measureSpace)
    expectation = tailIntegral ∧
      (expectation < (⊤ : ENNReal) ↔ tailIntegral < (⊤ : ENNReal)) ∧
      (expectation = (⊤ : ENNReal) ↔ tailIntegral = (⊤ : ENNReal)) := by
  dsimp
  have h_nonneg : 0 ≤ᵐ[μ] X := Filter.Eventually.of_forall hX_nonnegative
  have h := MeasureTheory.lintegral_eq_lintegral_meas_lt μ h_nonneg hX_measurable.aemeasurable
  exact ⟨h, h ▸ Iff.rfl, h ▸ Iff.rfl⟩
