import Mathlib

noncomputable section

open MeasureTheory

def IsIID (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω)
    (X : ℕ → Ω → ℝ) : Prop :=
  (∀ (i j : ℕ) (B : Set ℝ), MeasurableSet B →
    μ {ω : Ω | X i ω ∈ B} = μ {ω : Ω | X j ω ∈ B}) ∧
  (∀ (s : Finset ℕ) (A : ℕ → Set ℝ),
    (∀ i ∈ s, MeasurableSet (A i)) →
    μ {ω : Ω | ∀ i ∈ s, X i ω ∈ A i} =
      ∏ i ∈ s, μ {ω : Ω | X i ω ∈ A i})

theorem iid_hoeffding_mean_zero
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (h_iid : IsIID Ω μ X)
    (h_measurable : ∀ i : ℕ, Measurable (X i))
    (h_integrable : ∀ i : ℕ, Integrable (X i) μ)
    (c : ℝ) (hc : 0 < c)
    (h_tail : ∀ (N : ℕ) (a : Fin N → ℝ) (t : ℝ),
      0 ≤ t →
      0 < (∑ i : Fin N, ((a i) ^ (2 : ℕ) : ℝ)) →
      μ {ω : Ω | t ≤ |∑ i : Fin N, ((a i) * (X i.val ω) : ℝ)|} ≤
        ENNReal.ofReal
          ((2 : ℝ) * Real.exp
            (-c * (t ^ (2 : ℕ)) /
              (∑ i : Fin N, ((a i) ^ (2 : ℕ) : ℝ))))) :
    ∀ i : ℕ, (∫ ω : Ω, X i ω ∂μ) = (0 : ℝ) := by
  sorry
