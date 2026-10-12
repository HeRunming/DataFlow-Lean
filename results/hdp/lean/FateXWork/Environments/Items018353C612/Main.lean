import Mathlib

open MeasureTheory ProbabilityTheory

noncomputable section

namespace VarianceFormulas

abbrev RandomVector (Ω : Type*) (n : ℕ) [MeasurableSpace Ω] (μ : Measure Ω) :=
  Ω → EuclideanSpace ℝ (Fin n)

def expectation {Ω : Type*} {n : ℕ} [MeasurableSpace Ω]
    (μ : Measure Ω) (Z : RandomVector Ω n μ) : EuclideanSpace ℝ (Fin n) :=
  ∫ ω, Z ω ∂μ

theorem variance_formula_centered {Ω : Type*} {n : ℕ}
    [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (Z : RandomVector Ω n μ) (hZ : Measurable Z)
    (hZ_integrable : Integrable Z μ)
    (hZ_sq_integrable : Integrable (fun ω => ‖Z ω‖ ^ 2) μ) :
    (∫ ω, ‖Z ω - expectation μ Z‖ ^ 2 ∂μ) =
      (∫ ω, ‖Z ω‖ ^ 2 ∂μ) - ‖expectation μ Z‖ ^ 2 := by
  sorry

theorem variance_formula_independent_copy {Ω : Type*} {n : ℕ}
    [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (Z Z' : RandomVector Ω n μ) (hZ : Measurable Z) (hZ' : Measurable Z')
    (hZ_integrable : Integrable Z μ)
    (hZ'_integrable : Integrable Z' μ)
    (hZ_sq_integrable : Integrable (fun ω => ‖Z ω‖ ^ 2) μ)
    (hZ'_sq_integrable : Integrable (fun ω => ‖Z' ω‖ ^ 2) μ)
    (hIndep : IndepFun Z Z' μ) (hIdent : IdentDistrib Z Z' μ μ) :
    (∫ ω, ‖Z ω - expectation μ Z‖ ^ 2 ∂μ) =
      (1 / 2 : ℝ) * (∫ ω, ‖Z ω - Z' ω‖ ^ 2 ∂μ) := by
  sorry

end VarianceFormulas
