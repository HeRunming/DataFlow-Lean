import Mathlib

open MeasureTheory
open scoped BigOperators

universe u

namespace QuantitativeSmallBall

/-- Admissible scales for the source's Luxemburg psi-two norm. -/
def Psi2Admissible {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) (Y : Ω → ℝ) (t : ℝ) : Prop :=
  (0 : ℝ) < t ∧
    Integrable (fun ω : Ω => Real.exp ((Y ω / t) ^ (2 : ℕ))) μ ∧
    (∫ ω : Ω, Real.exp ((Y ω / t) ^ (2 : ℕ)) ∂μ) ≤ (2 : ℝ)

/-- Subgaussianity expressed using a finite exponential-square moment. -/
def IsSubgaussian {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) (Y : Ω → ℝ) : Prop :=
  ∃ t : ℝ, Psi2Admissible μ Y t

/-- The Luxemburg psi-two norm, used only for subgaussian variables below. -/
noncomputable def psi2Norm {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) (Y : Ω → ℝ) : ℝ :=
  sInf {t : ℝ | Psi2Admissible μ Y t}

/-- Joint independence, stated through measurable finite rectangles. -/
def JointlyIndependent {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) {N : ℕ} (X : Fin N → Ω → ℝ) : Prop :=
  ∀ (s : Finset (Fin N)) (B : Fin N → Set ℝ),
    (∀ i : Fin N, MeasurableSet (B i)) →
    μ {ω : Ω | ∀ i ∈ s, X i ω ∈ B i} =
      (∏ i ∈ s, μ {ω : Ω | X i ω ∈ B i} : ENNReal)

/-- The maximum psi-two norm of a finite family. -/
noncomputable def maxPsi2Norm {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) {N : ℕ} (X : Fin N → Ω → ℝ) : ℝ :=
  sSup (Set.range (fun i : Fin N => psi2Norm μ (X i)))

theorem quantitative_small_ball :
    ∃ c : ℝ, (0 : ℝ) < c ∧
      ∀ (Ω : Type u) [MeasurableSpace Ω]
        (μ : Measure Ω) [IsProbabilityMeasure μ]
        (N : ℕ),
        0 < N →
        ∀ (X : Fin N → Ω → ℝ) (a : Fin N → ℝ),
          (∀ i : Fin N, Measurable (X i)) →
          JointlyIndependent μ X →
          (∀ i : Fin N, IsSubgaussian μ (X i)) →
          (∀ i : Fin N, Integrable (X i) μ) →
          (∀ i : Fin N,
            Integrable (fun ω : Ω => (X i ω) ^ (2 : ℕ)) μ) →
          (∀ i : Fin N, (∫ ω : Ω, X i ω ∂μ) = (0 : ℝ)) →
          (∀ i : Fin N,
            (∫ ω : Ω, (X i ω) ^ (2 : ℕ) ∂μ) = (1 : ℝ)) →
          let K : ℝ := maxPsi2Norm μ X
          c / K ^ (4 : ℕ) ≤
            (μ {ω : Ω |
              (1 / 2 : ℝ) *
                  Real.sqrt (∑ i : Fin N, (a i) ^ (2 : ℕ) : ℝ) ≤
                |(∑ i : Fin N, a i * X i ω : ℝ)|}).toReal := by
  sorry

end QuantitativeSmallBall
