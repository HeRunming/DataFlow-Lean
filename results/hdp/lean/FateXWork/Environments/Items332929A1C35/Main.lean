import Mathlib

namespace SubgaussianVector

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The extended-valued scalar ψ₂ norm, with threshold 2. An empty set of admissible scales has infimum `⊤`. -/
noncomputable def scalarPsiTwoNorm (μ : MeasureTheory.Measure Ω) (Y : Ω → ℝ) : ENNReal :=
  sInf {r : ENNReal | ∃ c : ℝ, 0 < c ∧
    MeasureTheory.lintegral μ
      (fun ω => ENNReal.ofReal (Real.exp ((Y ω) ^ 2 / c ^ 2))) ≤ (2 : ENNReal) ∧
    r = ENNReal.ofReal c}

/-- The vector ψ₂ norm is the supremum of the scalar ψ₂ norms of unit-length projections. -/
noncomputable def vectorPsiTwoNorm {n : ℕ} (μ : MeasureTheory.Measure Ω)
    (X : Ω → Fin n → ℝ) : ENNReal :=
  sSup {r : ENNReal | ∃ u : Fin n → ℝ,
    ((∑ i : Fin n, (u i) ^ 2) : ℝ) = (1 : ℝ) ∧
    r = scalarPsiTwoNorm μ
      (fun ω => ((∑ i : Fin n, X ω i * u i) : ℝ))}

/-- A measurable random vector with finite vector ψ₂ norm. -/
def IsSubgaussianRandomVector {n : ℕ} (μ : MeasureTheory.Measure Ω)
    (X : Ω → Fin n → ℝ) : Prop :=
  Measurable X ∧ vectorPsiTwoNorm μ X < ⊤

theorem scalarPsiTwoNorm_projection_le {n : ℕ}
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (X : Ω → Fin n → ℝ) (hX : IsSubgaussianRandomVector μ X)
    (v : Fin n → ℝ) :
    scalarPsiTwoNorm μ
        (fun ω => ((∑ i : Fin n, X ω i * v i) : ℝ)) ≤
      vectorPsiTwoNorm μ X *
        ENNReal.ofReal (Real.sqrt (((∑ i : Fin n, (v i) ^ 2) : ℝ))) := by
  sorry

end SubgaussianVector
