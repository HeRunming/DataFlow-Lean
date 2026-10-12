import Mathlib

open MeasureTheory

noncomputable def psiOneNorm {Ω : Type*} [MeasurableSpace Ω]
    (X : Ω → ℝ) (μ : Measure Ω) : ℝ :=
  sInf {K : ℝ | 0 < K ∧
    Integrable (fun ω => Real.exp (|X ω| / K)) μ ∧
    (∫ ω, Real.exp (|X ω| / K) ∂μ) ≤ (2 : ℝ)}

def Subexponential {Ω : Type*} [MeasurableSpace Ω]
    (X : Ω → ℝ) (μ : Measure Ω) : Prop :=
  ∃ K : ℝ, 0 < K ∧
    Integrable (fun ω => Real.exp (|X ω| / K)) μ ∧
    (∫ ω, Real.exp (|X ω| / K) ∂μ) ≤ (2 : ℝ)

noncomputable def maxAbs {Ω : Type*} {n : ℕ}
    (X : Fin (n + 1) → Ω → ℝ) (ω : Ω) : ℝ :=
  Finset.univ.sup'
    ⟨(0 : Fin (n + 1)), Finset.mem_univ _⟩
    (fun i => |X i ω|)

/-- (a) Centering for the subexponential Orlicz norm. -/
theorem subexponential_centering :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
        [IsProbabilityMeasure μ] (X : Ω → ℝ),
        Measurable X → Subexponential X μ →
        psiOneNorm (fun ω => X ω - ∫ ω, X ω ∂μ) μ ≤
          C * psiOneNorm X μ := by
  sorry

/-- (b) An expected-maximum inequality for a nonempty finite family. -/
theorem subexponential_maximal_inequality :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
        [IsProbabilityMeasure μ] (n : ℕ)
        (X : Fin (n + 1) → Ω → ℝ) (K : ℝ),
        0 ≤ K →
        (∀ i : Fin (n + 1),
          Measurable (X i) ∧ Subexponential (X i) μ ∧
            psiOneNorm (X i) μ ≤ K) →
        (∫ ω, maxAbs X ω ∂μ) ≤
          C * Real.log ((n : ℝ) + (2 : ℝ)) * K := by
  sorry

/-- Convex dominance, including integrability for expectation comparisons. -/
def ConvexlyDominated {Ω : Type*} [MeasurableSpace Ω]
    (X Y : Ω → ℝ) (μ : Measure Ω) : Prop :=
  ∀ f : ℝ → ℝ, Continuous f → ConvexOn ℝ Set.univ f →
    Integrable (fun ω => f (Y ω)) μ →
      Integrable (fun ω => f (X ω)) μ ∧
        (∫ ω, f (X ω) ∂μ) ≤ (∫ ω, f (Y ω) ∂μ)

/-- (c) Convex dominance preserves subexponentiality and bounds its norm. -/
theorem subexponential_convex_dominance
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X Y : Ω → ℝ)
    (hX : Measurable X) (hY : Measurable Y)
    (hYsub : Subexponential Y μ)
    (hdom : ConvexlyDominated X Y μ) :
    Subexponential X μ ∧ psiOneNorm X μ ≤ psiOneNorm Y μ := by
  sorry
