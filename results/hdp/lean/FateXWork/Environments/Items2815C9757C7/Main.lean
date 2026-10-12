import Mathlib

open MeasureTheory

namespace ProbabilityTailMoment

variable {Ω : Type*} [MeasurableSpace Ω]

def TailBound (μ : Measure Ω) (X : Ω → ℝ) (K : ℝ) : Prop :=
  0 < K ∧
    ∀ (t : ℝ), 0 ≤ t →
      μ.real {ω : Ω | t ≤ |X ω|} ≤ (2 : ℝ) * Real.exp (-t / K)

def MomentBound (μ : Measure Ω) (X : Ω → ℝ) (K : ℝ) : Prop :=
  0 < K ∧
    ∀ (p : ℝ), 1 ≤ p →
      Integrable (fun ω : Ω => Real.rpow |X ω| p) μ ∧
        Real.rpow (∫ ω : Ω, Real.rpow |X ω| p ∂μ) (1 / p) ≤ K * p

def AbsMGFBound (μ : Measure Ω) (X : Ω → ℝ) (K : ℝ) : Prop :=
  0 < K ∧
    Integrable (fun ω : Ω => Real.exp (|X ω| / K)) μ ∧
      (∫ ω : Ω, Real.exp (|X ω| / K) ∂μ) ≤ (2 : ℝ)

def Centered (μ : Measure Ω) (X : Ω → ℝ) : Prop :=
  Integrable X μ ∧ (∫ ω : Ω, X ω ∂μ) = 0

def MGFBound (μ : Measure Ω) (X : Ω → ℝ) (K : ℝ) : Prop :=
  0 < K ∧
    ∀ (coeff : ℝ), |coeff| ≤ 1 / K →
      Integrable (fun ω : Ω => Real.exp (coeff * X ω)) μ ∧
        (∫ ω : Ω, Real.exp (coeff * X ω) ∂μ) ≤
          Real.exp (K ^ 2 * coeff ^ 2)

theorem tails_iff_moments_iff_abs_mgf
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ)
    (hX : Measurable X) :
    ((∃ K₁ : ℝ, TailBound μ X K₁) ↔
        (∃ K₂ : ℝ, MomentBound μ X K₂)) ∧
      ((∃ K₂ : ℝ, MomentBound μ X K₂) ↔
        (∃ K₃ : ℝ, AbsMGFBound μ X K₃)) ∧
      ((∃ K₁ : ℝ, TailBound μ X K₁) ↔
        (∃ K₃ : ℝ, AbsMGFBound μ X K₃)) := by
  sorry

theorem centered_tails_moments_abs_mgf_mgf
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ)
    (hX : Measurable X)
    (hcentered : Centered μ X) :
    ((∃ K₁ : ℝ, TailBound μ X K₁) ↔
        (∃ K₂ : ℝ, MomentBound μ X K₂)) ∧
      ((∃ K₂ : ℝ, MomentBound μ X K₂) ↔
        (∃ K₃ : ℝ, AbsMGFBound μ X K₃)) ∧
      ((∃ K₃ : ℝ, AbsMGFBound μ X K₃) ↔
        (∃ K₄ : ℝ, MGFBound μ X K₄)) ∧
      ((∃ K₁ : ℝ, TailBound μ X K₁) ↔
        (∃ K₄ : ℝ, MGFBound μ X K₄)) := by
  sorry

theorem absolute_parameter_comparison
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ)
    (hX : Measurable X) :
    ∃ C : ℝ, 0 < C ∧
      (∀ (K₁ : ℝ), TailBound μ X K₁ →
        MomentBound μ X (C * K₁) ∧ AbsMGFBound μ X (C * K₁)) ∧
      (∀ (K₂ : ℝ), MomentBound μ X K₂ →
        TailBound μ X (C * K₂) ∧ AbsMGFBound μ X (C * K₂)) ∧
      (∀ (K₃ : ℝ), AbsMGFBound μ X K₃ →
        TailBound μ X (C * K₃) ∧ MomentBound μ X (C * K₃)) := by
  sorry

theorem centered_absolute_parameter_comparison
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ)
    (hX : Measurable X)
    (hcentered : Centered μ X) :
    ∃ C : ℝ, 0 < C ∧
      (∀ (K₁ : ℝ), TailBound μ X K₁ →
        MomentBound μ X (C * K₁) ∧
          AbsMGFBound μ X (C * K₁) ∧
          MGFBound μ X (C * K₁)) ∧
      (∀ (K₂ : ℝ), MomentBound μ X K₂ →
        TailBound μ X (C * K₂) ∧
          AbsMGFBound μ X (C * K₂) ∧
          MGFBound μ X (C * K₂)) ∧
      (∀ (K₃ : ℝ), AbsMGFBound μ X K₃ →
        TailBound μ X (C * K₃) ∧
          MomentBound μ X (C * K₃) ∧
          MGFBound μ X (C * K₃)) ∧
      (∀ (K₄ : ℝ), MGFBound μ X K₄ →
        TailBound μ X (C * K₄) ∧
          MomentBound μ X (C * K₄) ∧
          AbsMGFBound μ X (C * K₄)) := by
  sorry

end ProbabilityTailMoment
