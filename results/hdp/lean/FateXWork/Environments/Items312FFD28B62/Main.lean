import Mathlib

open MeasureTheory
open ProbabilityTheory

/-- Independent mean-zero isotropic random vectors in `ℝ^n` satisfy
    `𝔼 ‖X - Y‖₂² = 2n`. -/
theorem expected_norm_sq_sub_eq_two_mul_dim
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    (n : ℕ)
    (X Y : Ω → EuclideanSpace ℝ (Fin n))
    (hX_integrable : Integrable X μ)
    (hY_integrable : Integrable Y μ)
    (hX_mean : ∫ ω, X ω ∂μ = (0 : EuclideanSpace ℝ (Fin n)))
    (hY_mean : ∫ ω, Y ω ∂μ = (0 : EuclideanSpace ℝ (Fin n)))
    (hX_isotropic :
      ∀ i : Fin n, ∀ j : Fin n,
        ∫ ω, (X ω) i * (X ω) j ∂μ = if i = j then (1 : ℝ) else (0 : ℝ))
    (hY_isotropic :
      ∀ i : Fin n, ∀ j : Fin n,
        ∫ ω, (Y ω) i * (Y ω) j ∂μ = if i = j then (1 : ℝ) else (0 : ℝ))
    (hXY_independent : IndepFun X Y μ) :
    ∫ ω, ‖X ω - Y ω‖ ^ 2 ∂μ = (2 : ℝ) * (n : ℝ) := by
  sorry
