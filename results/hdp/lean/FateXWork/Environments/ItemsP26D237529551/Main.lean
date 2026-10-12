import Mathlib.Probability.ProbabilityMassFunction.Binomial
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Data.Fintype.BigOperators

open scoped BigOperators
open MeasureTheory ProbabilityTheory

namespace SourceFormalization

def sumX {Ω : Type*} {N : ℕ} (X : Fin N → Ω → Bool) (ω : Ω) : ℕ :=
  (∑ i : Fin N, (if X i ω then 1 else 0) : ℕ)

def IsBernoulli
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (p : NNReal)
    (X : Ω → Bool) : Prop :=
  Measurable X ∧
    μ {ω | X ω = true} = (p : ENNReal) ∧
    μ {ω | X ω = false} = 1 - (p : ENNReal)

def HasBinomialDistribution
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (N : ℕ)
    (p : NNReal) (S : Ω → ℕ) : Prop :=
  Measurable S ∧
    ∀ k : Fin (N + 1),
      μ {ω | S ω = (k : ℕ)} =
        (p : ENNReal) ^ (k : ℕ) *
          (1 - (p : ENNReal)) ^ (N - (k : ℕ)) *
          (N.choose (k : ℕ) : ENNReal)

theorem sum_independent_bernoulli_has_binomial_distribution
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (N : ℕ) (p : NNReal) (hp : p ≤ 1)
    (X : Fin N → Ω → Bool)
    (hX_meas : ∀ i : Fin N, Measurable (X i))
    (hX_bernoulli : ∀ i : Fin N, IsBernoulli μ p (X i))
    (hX_independent : iIndepFun X μ) :
    HasBinomialDistribution μ N p (sumX X) := by
  sorry

end SourceFormalization
