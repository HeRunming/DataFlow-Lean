import Mathlib.Probability.Distributions.Gaussian.Basic
import Mathlib.Probability.Independence.Basic

open MeasureTheory ProbabilityTheory

universe u

namespace StandardNormalDistribution

def HasStandardNormalDistribution
    {n : Nat} {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) (Z : Fin n → Ω → ℝ) : Prop :=
  (∀ i : Fin n, Measurable (Z i)) ∧
    iIndepFun Z P ∧
    (∀ i : Fin n, Measure.map (Z i) P = ProbabilityTheory.gaussianReal (0 : ℝ) (1 : NNReal))

theorem standardNormalDistribution_iff
    {n : Nat} {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) (Z : Fin n → Ω → ℝ) :
    HasStandardNormalDistribution P Z ↔
      ((∀ i : Fin n, Measurable (Z i)) ∧
        iIndepFun Z P ∧
        (∀ i : Fin n, Measure.map (Z i) P = ProbabilityTheory.gaussianReal (0 : ℝ) (1 : NNReal))) := by
  set_option maxHeartbeats 5000 in
    first | (rfl; done) | (assumption; done) | (simp; done) | (norm_num; done) | (omega; done) | (linarith; done) | (ring; done) | (simp_all [HasStandardNormalDistribution]; done)

end StandardNormalDistribution
