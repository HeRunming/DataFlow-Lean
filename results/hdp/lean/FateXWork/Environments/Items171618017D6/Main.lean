import Mathlib

open MeasureTheory Filter
open scoped BigOperators Topology

universe u

private theorem iid_pairwise_indep
    {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ)
    (h_measurable : ∀ i : ℕ, Measurable (X i))
    (h_independent : ∀ (I : Finset ℕ) (A : ℕ → Set ℝ), (∀ i ∈ I, MeasurableSet (A i)) → P {ω : Ω | ∀ i ∈ I, X i ω ∈ A i} = (∏ i ∈ I, P (X i ⁻¹' A i) : ENNReal)) :
    Pairwise (Function.onFun (fun x1 x2 => ProbabilityTheory.IndepFun x1 x2 P) X) := by
  intro i j hij
  change ProbabilityTheory.IndepFun (X i) (X j) P
  rw [ProbabilityTheory.indepFun_iff_measure_inter_preimage_eq_mul]
  intro A B hA hB
  have h := h_independent ({i, j} : Finset ℕ)
      (fun k => if k = i then A else if k = j then B else Set.univ) (by
        intro k hk
        simp only [Finset.mem_insert, Finset.mem_singleton] at hk
        rcases hk with rfl | rfl
        · simp [hA]
        · simp [hij, Ne.symm hij, hB])
  simpa [hij, Ne.symm hij] using h

/-- The strong law for an i.i.d. sequence with a finite real mean.
The Lean variable `X i` represents the source variable `X_{i+1}`. -/
theorem iid_sample_mean_tendsto_almost_surely
    {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (μ : ℝ)
    (h_measurable : ∀ i : ℕ, Measurable (X i))
    (h_integrable : ∀ i : ℕ, Integrable (X i) P)
    (h_mean : ∀ i : ℕ, (∫ ω, X i ω ∂P) = μ)
    (h_independent :
      ∀ (I : Finset ℕ) (A : ℕ → Set ℝ),
        (∀ i ∈ I, MeasurableSet (A i)) →
        P {ω : Ω | ∀ i ∈ I, X i ω ∈ A i} =
          (∏ i ∈ I, P (X i ⁻¹' A i) : ENNReal))
    (h_identically_distributed :
      ∀ (i : ℕ) (B : Set ℝ), MeasurableSet B →
        P (X i ⁻¹' B) = P (X 0 ⁻¹' B)) :
    ∀ᵐ ω ∂P,
      Filter.Tendsto
        (fun N : ℕ =>
          (∑ i ∈ Finset.range N, X i ω : ℝ) / (N : ℝ))
        Filter.atTop (nhds μ) := by
  have hd : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) P P := by
    intro i
    refine ⟨(h_measurable i).aemeasurable, (h_measurable 0).aemeasurable, ?_⟩
    apply Measure.ext
    intro B hB
    rw [Measure.map_apply (h_measurable i) hB, Measure.map_apply (h_measurable 0) hB]
    exact h_identically_distributed i B hB
  simpa only [h_mean 0] using
    ProbabilityTheory.strong_law_ae_real X (h_integrable 0)
      (iid_pairwise_indep P X h_measurable h_independent) hd
