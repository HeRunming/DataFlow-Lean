import Mathlib

open MeasureTheory

/--
Source proof: the text states Jensen's inequality and notes that the finite-valued
case follows from the finite convex-combination inequality, while the general case
is obtained by approximation.
Prover notes: this declaration records the scalar expectation form using a
probability measure; the hypotheses ensure that both integrals are meaningful.
-/
theorem jensen_inequality_scalar
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (f : ℝ → ℝ)
    (hf : ConvexOn ℝ Set.univ f)
    (hX : Integrable X μ) (hXf : Integrable (fun ω => f (X ω)) μ) :
    f (∫ ω, X ω ∂μ) ≤ ∫ ω, f (X ω) ∂μ := by
  sorry

/--
Source proof: the paragraph explicitly says that (1.18) extends to random
vectors in `ℝⁿ`; its finite-valued instance is proved by finite convex
combinations and the general statement follows by approximation.
Prover notes: `E` is a finite-dimensional real normed space, and the statement
uses Bochner expectation in the standard probability-measure formulation.
-/
theorem jensen_inequality_vector
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → E) (f : E → ℝ)
    (hf : ConvexOn ℝ Set.univ f)
    (hX : Integrable X μ) (hXf : Integrable (fun ω => f (X ω)) μ) :
    f (∫ ω, X ω ∂μ) ≤ ∫ ω, f (X ω) ∂μ := by
  sorry

/--
Source proof: equation (1.19) is obtained from (1.18) by taking `f` to be
any norm, since norms are convex.
Prover notes: this is the norm consequence for a finite-dimensional random
vector, with Bochner integrability of the vector and its norm.
-/
theorem norm_integral_le_integral_norm
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → E) (hX : Integrable X μ) :
    ‖∫ ω, X ω ∂μ‖ ≤ ∫ ω, ‖X ω‖ ∂μ := by
  sorry
