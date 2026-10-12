import Mathlib

open MeasureTheory

noncomputable section

namespace Psi2Source

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Positive scales with a finite exponential-square expectation at most two. -/
def Psi2Admissible (μ : Measure Ω) (X : Ω → ℝ) : Set ℝ :=
  {t : ℝ | (0 : ℝ) < t ∧
    Integrable (fun ω : Ω => Real.exp ((X ω / t) ^ (2 : ℕ))) μ ∧
    (∫ ω : Ω, Real.exp ((X ω / t) ^ (2 : ℕ)) ∂μ) ≤ (2 : ℝ)}

/-- The finite Luxemburg psi-two norm, specified by its greatest-lower-bound property. -/
def HasPsi2Norm (μ : Measure Ω) (X : Ω → ℝ) (r : ℝ) : Prop :=
  IsGLB (Psi2Admissible μ X) r

/-- The finite essential supremum of the absolute value. -/
def HasEssentialSupNorm (μ : Measure Ω) (X : Ω → ℝ) (b : ℝ) : Prop :=
  IsGLB {B : ℝ | (0 : ℝ) ≤ B ∧ ∀ᵐ ω : Ω ∂μ, |X ω| ≤ B} b

/-- Equal probability at minus one and one. -/
def IsRademacher (μ : Measure Ω) (X : Ω → ℝ) : Prop :=
  (∀ᵐ ω : Ω ∂μ, X ω = (-1 : ℝ) ∨ X ω = (1 : ℝ)) ∧
  μ {ω : Ω | X ω = (1 : ℝ)} =
    ENNReal.ofReal ((1 : ℝ) / (2 : ℝ))

/-- The centered normal law characterized by its finite MGF at every real argument. -/
def HasCenteredNormalLaw (μ : Measure Ω) (X : Ω → ℝ) (σ : ℝ) : Prop :=
  ∀ t : ℝ,
    Integrable (fun ω : Ω => Real.exp (t * X ω)) μ ∧
    (∫ ω : Ω, Real.exp (t * X ω) ∂μ) =
      Real.exp ((σ ^ (2 : ℕ) * t ^ (2 : ℕ)) / (2 : ℝ))

/-- A Bernoulli law, with parameter bounds supplied by the theorem. -/
def HasBernoulliLaw (μ : Measure Ω) (X : Ω → ℝ) (p : ℝ) : Prop :=
  (∀ᵐ ω : Ω ∂μ, X ω = (0 : ℝ) ∨ X ω = (1 : ℝ)) ∧
  μ {ω : Ω | X ω = (1 : ℝ)} = ENNReal.ofReal p

/-- (a) The literal source formula, including the signed constant. -/
theorem constant
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : Measurable X)
    (c : ℝ) (hc : ∀ᵐ ω : Ω ∂μ, X ω = c) :
    HasPsi2Norm μ X (c / Real.sqrt (Real.log (2 : ℝ))) := by sorry

/-- (b) The almost-sure boundedness estimate. -/
theorem bounded
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : Measurable X)
    (hbounded : ∃ B : ℝ, ∀ᵐ ω : Ω ∂μ, |X ω| ≤ B) :
    ∃ r b : ℝ,
      HasPsi2Norm μ X r ∧ HasEssentialSupNorm μ X b ∧
      r ≤ b / Real.sqrt (Real.log (2 : ℝ)) := by sorry

/-- (c) The Rademacher value. -/
theorem rademacher
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : Measurable X)
    (hLaw : IsRademacher μ X) :
    HasPsi2Norm μ X
      ((1 : ℝ) / Real.sqrt (Real.log (2 : ℝ))) := by sorry

/-- (d) The literal source formula, without an added sign restriction on sigma. -/
theorem normal
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : Measurable X)
    (σ : ℝ)
    (hLaw : HasCenteredNormalLaw μ X σ) :
    HasPsi2Norm μ X
      (σ * Real.sqrt ((8 : ℝ) / (3 : ℝ))) := by sorry

/-- (e) The Bernoulli formula on the ordinary real expression's domain. -/
theorem bernoulli
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : Measurable X)
    (p : ℝ) (hp0 : (0 : ℝ) < p) (hp1 : p ≤ (1 : ℝ))
    (hLaw : HasBernoulliLaw μ X p) :
    HasPsi2Norm μ X
      ((1 : ℝ) / Real.sqrt (Real.log ((1 : ℝ) + (1 : ℝ) / p))) := by sorry

end Psi2Source
