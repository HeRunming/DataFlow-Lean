import Mathlib

open MeasureTheory

universe u

def IsBernoulli (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → Bool) (p : ℝ) : Prop :=
  Measurable X ∧
    μ (X ⁻¹' ({true} : Set Bool)) = ENNReal.ofReal p

def BernoulliSetup (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω)
    (X : ℕ → Ω → Bool) (p : ℝ) : Prop :=
  IsProbabilityMeasure μ ∧
    (0 : ℝ) < p ∧
    p < (1 : ℝ) ∧
    ∀ i : ℕ, IsBernoulli Ω μ (X i) p

theorem bernoulli_setup
    (Ω : Type u) [MeasurableSpace Ω]
    (μ : Measure Ω)
    (X : ℕ → Ω → Bool)
    (p : ℝ)
    (hμ : IsProbabilityMeasure μ)
    (hp0 : (0 : ℝ) < p)
    (hp1 : p < (1 : ℝ))
    (hX : ∀ i : ℕ, IsBernoulli Ω μ (X i) p) :
    BernoulliSetup Ω μ X p := by
  sorry
