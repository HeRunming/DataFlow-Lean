import Mathlib

open MeasureTheory

universe u v

namespace TailComparison

/-- Tail comparison for random variables, possibly on different spaces. -/
def TailDominated
    {Ω : Type u} {Γ : Type v}
    [MeasurableSpace Ω] [MeasurableSpace Γ]
    (coeff : ENNReal) (μ : Measure Ω) (ν : Measure Γ)
    (X : Ω → ℝ) (Y : Γ → ℝ) : Prop :=
  ∀ t : ℝ, μ {ω : Ω | t ≤ X ω} ≤ coeff * ν {ω : Γ | t ≤ Y ω}

/-- Positive scales admissible for the exponential-square Luxemburg norm. -/
def Psi2Admissible
    {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℝ) (c : ℝ) : Prop :=
  (0 : ℝ) < c ∧
    Integrable (fun ω : Ω => Real.exp ((X ω / c) ^ (2 : ℕ))) μ ∧
    (∫ ω : Ω, Real.exp ((X ω / c) ^ (2 : ℕ)) ∂μ) ≤ (2 : ℝ)

/-- Noncentered subgaussianity in the exponential-square sense. -/
def Subgaussian
    {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℝ) : Prop :=
  Measurable X ∧ ∃ c : ℝ, Psi2Admissible μ X c

/-- The real-valued psi₂ norm, used in conclusions only for subgaussian variables. -/
noncomputable def psi2Norm
    {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℝ) : ℝ :=
  sInf {c : ℝ | Psi2Admissible μ X c}

/-- Standard normal law specified by its finite MGF at every real argument. -/
def StandardNormal
    {Γ : Type v} [MeasurableSpace Γ]
    (ν : Measure Γ) (g : Γ → ℝ) : Prop :=
  Measurable g ∧
    ∀ t : ℝ,
      Integrable (fun ω : Γ => Real.exp (t * g ω)) ν ∧
      (∫ ω : Γ, Real.exp (t * g ω) ∂ν) =
        Real.exp (t ^ (2 : ℕ) / (2 : ℝ))

/-- Part (a): qualitative equivalence. -/
theorem part_a_iff
    {Ω : Type u} {Γ : Type v}
    [MeasurableSpace Ω] [MeasurableSpace Γ]
    (μ : Measure Ω) (ν : Measure Γ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (X : Ω → ℝ) (g : Γ → ℝ)
    (hX : Measurable X) (hg : StandardNormal ν g) :
    Subgaussian μ X ↔
      ∃ K : ℝ, (0 : ℝ) < K ∧
        TailDominated (2 : ENNReal) μ ν
          (fun ω : Ω => |X ω|) (fun ω : Γ => K * |g ω|) := by sorry

/--
Part (a): both quantitative assertions with a universal constant.
The literal strict positivity of K is retained, including the source's
zero-norm obstruction documented in the accompanying source contract.
-/
theorem part_a_quantitative_literal :
    ∃ C : ℝ, (0 : ℝ) < C ∧
      ∀ {Ω : Type u} {Γ : Type v}
        [MeasurableSpace Ω] [MeasurableSpace Γ]
        (μ : Measure Ω) (ν : Measure Γ)
        [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
        (X : Ω → ℝ) (g : Γ → ℝ),
        Measurable X → StandardNormal ν g →
        (Subgaussian μ X →
          ∃ K : ℝ, (0 : ℝ) < K ∧
            K ≤ C * psi2Norm μ X ∧
            TailDominated (2 : ENNReal) μ ν
              (fun ω : Ω => |X ω|) (fun ω : Γ => K * |g ω|)) ∧
        (∀ K : ℝ, (0 : ℝ) < K →
          TailDominated (2 : ENNReal) μ ν
            (fun ω : Ω => |X ω|) (fun ω : Γ => K * |g ω|) →
          Subgaussian μ X ∧ psi2Norm μ X ≤ C * K) := by sorry

/-- Part (b): the constant-one random variable is an example of failure. -/
theorem part_b_constant_one
    {Ω : Type u} {Γ : Type v}
    [MeasurableSpace Ω] [MeasurableSpace Γ]
    (μ : Measure Ω) (ν : Measure Γ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (g : Γ → ℝ) (hg : StandardNormal ν g) :
    Measurable (fun _ : Ω => (1 : ℝ)) ∧
    Subgaussian μ (fun _ : Ω => (1 : ℝ)) ∧
    ∀ K : ℝ, (0 : ℝ) < K →
      ¬ TailDominated (1 : ENNReal) μ ν
        (fun _ : Ω => |(1 : ℝ)|) (fun ω : Γ => K * |g ω|) := by sorry

end TailComparison
