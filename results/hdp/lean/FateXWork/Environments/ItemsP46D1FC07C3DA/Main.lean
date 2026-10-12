import Mathlib

open MeasureTheory

universe u

namespace SourceSubgaussian

/-- Positive real scales satisfying the source's exponential-moment bound.
The subtype ensures that X is a measurable real random variable. -/
def admissibleScales {Ω : Type u} [MeasurableSpace Ω]
    (μ : ProbabilityMeasure Ω)
    (X : {f : Ω → ℝ // Measurable f}) : Set ENNReal :=
  {r : ENNReal | ∃ K : ℝ,
    (0 : ℝ) < K ∧
    r = ENNReal.ofReal K ∧
    (∫⁻ ω : Ω, ENNReal.ofReal
      (Real.exp ((X.val ω) ^ (2 : ℕ) / K ^ (2 : ℕ)))
      ∂(μ : Measure Ω)) ≤ (2 : ENNReal)}

/-- The source-defined subgaussian norm, using an explicitly extended-valued
convention: the infimum of an empty admissible set is infinity. -/
noncomputable def subgaussianNorm {Ω : Type u} [MeasurableSpace Ω]
    (μ : ProbabilityMeasure Ω)
    (X : {f : Ω → ℝ // Measurable f}) : ENNReal :=
  sInf (admissibleScales μ X)

/-- Equation (2.18), with positive real scales embedded into ENNReal. -/
theorem subgaussianNorm_eq_sInf {Ω : Type u} [MeasurableSpace Ω]
    (μ : ProbabilityMeasure Ω)
    (X : {f : Ω → ℝ // Measurable f}) :
    subgaussianNorm μ X =
      sInf {r : ENNReal | ∃ K : ℝ,
        (0 : ℝ) < K ∧
        r = ENNReal.ofReal K ∧
        (∫⁻ ω : Ω, ENNReal.ofReal
          (Real.exp ((X.val ω) ^ (2 : ℕ) / K ^ (2 : ℕ)))
          ∂(μ : Measure Ω)) ≤ (2 : ENNReal)} := by sorry

end SourceSubgaussian
