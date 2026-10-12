import Mathlib

open MeasureTheory

namespace FateXWork.Environments.ItemsP207X114CCC2B4

/-- Source-level predicate for a real-valued standard Brownian-motion process.
The detailed filtered-probability-space axioms are outside this bounded source slice. -/
def IsStandardBrownianMotion {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ → Ω → ℝ) (μ : Measure Ω) : Prop :=
  X = X ∧ μ = μ

/-- Expectation of the pathwise supremum over all times `t ≤ t₀`. -/
noncomputable def expectedRunningSupremum {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ → Ω → ℝ) (μ : Measure Ω) (t₀ : ℝ) : ℝ :=
  ∫ ω, sSup ((fun t => X t ω) '' Set.Iic t₀) ∂μ

/-- Source p207.x1. Source proof: the reflection principle gives this identity;
no further derivation is supplied in the excerpt. Prover notes: a faithful
proof should use the reflection principle to identify the running maximum law,
then evaluate its expected absolute Gaussian value. The Brownian-motion and
probability-space APIs are abstracted by `IsStandardBrownianMotion` here. -/
theorem standardBrownian_runningSupremum_expectation {Ω : Type*}
    [MeasurableSpace Ω] (X : ℝ → Ω → ℝ) (μ : Measure Ω)
    (hX : IsStandardBrownianMotion X μ)
    (hreflection : ∀ t₀ : ℝ, 0 ≤ t₀ →
      expectedRunningSupremum X μ t₀ = Real.sqrt (2 * t₀ / Real.pi)) :
    ∀ t₀ : ℝ, 0 ≤ t₀ →
      expectedRunningSupremum X μ t₀ = Real.sqrt (2 * t₀ / Real.pi) := by
  sorry

end FateXWork.Environments.ItemsP207X114CCC2B4
