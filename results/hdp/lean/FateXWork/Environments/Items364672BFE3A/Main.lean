import Mathlib

open scoped BigOperators
open MeasureTheory

namespace HDPItem.Items364672BFE3A

namespace MaxCutRounding

private def dot {n : ℕ} (u v : Fin n → ℝ) : ℝ :=
  ∑ i ∈ (Finset.univ : Finset (Fin n)), u i * v i

private noncomputable def cutValue {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → Bool) : ℝ :=
  ∑ i ∈ (Finset.univ : Finset (Fin n)),
    ∑ j ∈ (Finset.univ : Finset (Fin n)),
      A i j * (if x i != x j then (1 / 2 : ℝ) else (0 : ℝ))

private noncomputable def sdpValue {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (X : Fin n → Fin n → ℝ) : ℝ :=
  ∑ i ∈ (Finset.univ : Finset (Fin n)),
    ∑ j ∈ (Finset.univ : Finset (Fin n)),
      A i j * ((1 : ℝ) - dot (X i) (X j)) / (4 : ℝ)

private def Feasible {n : ℕ} (X : Fin n → Fin n → ℝ) : Prop :=
  ∀ i : Fin n, dot (X i) (X i) = (1 : ℝ)

private noncomputable def sdp {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  sSup {r : ℝ | ∃ X : Fin n → Fin n → ℝ,
    Feasible X ∧ r = sdpValue A X}

private noncomputable def maxcut {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  sSup {r : ℝ | ∃ x : Fin n → Bool, r = cutValue A x}

private noncomputable def IsSDPSolution {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (X : Fin n → Fin n → ℝ) : Prop :=
  Feasible X ∧ sdpValue A X = sdp A

private def IsStandardGaussian {n : ℕ}
    (μ : Measure (Fin n → ℝ)) : Prop :=
  ∀ (v : Fin n → ℝ) (t : ℝ),
    (∫ ω : Fin n → ℝ, Real.cos (t * dot v ω) ∂μ) =
        Real.exp (-(t * t * dot v v) / (2 : ℝ)) ∧
    (∫ ω : Fin n → ℝ, Real.sin (t * dot v ω) ∂μ) = (0 : ℝ)

private def IsRandomizedRounding {n : ℕ}
    (X : Fin n → Fin n → ℝ)
    (x : (Fin n → ℝ) → Fin n → Bool) : Prop :=
  ∀ (ω : Fin n → ℝ) (i : Fin n),
    x ω i = decide ((0 : ℝ) ≤ dot (X i) ω)

theorem expected_cut_ge_sdp_ge_maxcut
    {n : ℕ} (G : SimpleGraph (Fin n))
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i j : Fin n,
      (G.Adj i j → A i j = (1 : ℝ)) ∧
      (¬ G.Adj i j → A i j = (0 : ℝ)))
    (X : Fin n → Fin n → ℝ)
    (hX : IsSDPSolution A X)
    (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ]
    (hμ : IsStandardGaussian μ)
    (x : (Fin n → ℝ) → Fin n → Bool)
    (hx : IsRandomizedRounding X x)
    (hx_measurable : Measurable x) :
    (∫ ω : Fin n → ℝ, cutValue A (x ω) ∂μ) ≥
        (0.878 : ℝ) * sdp A ∧
      (0.878 : ℝ) * sdp A ≥ (0.878 : ℝ) * maxcut A := by
  sorry

end MaxCutRounding

end HDPItem.Items364672BFE3A
