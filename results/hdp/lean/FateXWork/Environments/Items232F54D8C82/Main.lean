import Mathlib

open MeasureTheory ProbabilityTheory

noncomputable def sourcePsi2Norm {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℝ) : ℝ :=
  sInf {c : ℝ | ∃ q : NNReal, (q : ℝ) = c ∧ ProbabilityTheory.HasSubgaussianMGF X q μ}

def sourceSubgaussian {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℝ) : Prop :=
  ∃ q : NNReal, ProbabilityTheory.HasSubgaussianMGF X q μ

theorem independent_meanZero_subgaussian_add_sourcePsi2Norm
    : ∃ C : ℝ, 0 < C ∧
        ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
          (X Y : Ω → ℝ),
          Measurable X →
          Measurable Y →
          Integrable X μ →
          Integrable Y μ →
          (∫ ω, X ω ∂μ) = (0 : ℝ) →
          (∫ ω, Y ω ∂μ) = (0 : ℝ) →
          ProbabilityTheory.IndepFun X Y μ →
          sourceSubgaussian μ X →
          sourceSubgaussian μ Y →
          sourcePsi2Norm μ (fun ω => X ω + Y ω) ≤
            C * (sourcePsi2Norm μ X + sourcePsi2Norm μ Y) := by
  sorry
