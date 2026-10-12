import Mathlib

open MeasureTheory ProbabilityTheory
open scoped BigOperators

universe u

private theorem rademacher_zero_variance {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) (N : ℕ) (X : Fin N → Ω → ℝ) (a : Fin N → ℝ)
    (h : ∑ i, (a i)^2 = 0) (t : ℝ) (ht : 0 < t) :
    (μ {ω | t ≤ |∑ i, a i * X i ω|}).toReal = 0 := by
  have ha : ∀ i, a i = 0 := by
    intro i
    have hi : (a i)^2 ≤ ∑ j, (a j)^2 :=
      Finset.single_le_sum (fun j _ => sq_nonneg (a j)) (Finset.mem_univ i)
    rw [h] at hi
    nlinarith [sq_nonneg (a i)]
  simp [ha, not_le.mpr ht]

private theorem rademacher_ae_sign {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (hm : Measurable X)
    (hp : μ {ω | X ω = 1} = (1 / 2 : ENNReal))
    (hn : μ {ω | X ω = -1} = (1 / 2 : ENNReal)) :
    ∀ᵐ ω ∂μ, X ω = 1 ∨ X ω = -1 := by
  have hmp : MeasurableSet {ω | X ω = (1 : ℝ)} := measurableSet_eq_fun hm measurable_const
  have hmn : MeasurableSet {ω | X ω = (-1 : ℝ)} := measurableSet_eq_fun hm measurable_const
  have hd : Disjoint {ω | X ω = (1 : ℝ)} {ω | X ω = (-1 : ℝ)} := by
    rw [Set.disjoint_left]
    intro ω h₁ h₂
    simp only [Set.mem_setOf_eq] at h₁ h₂
    linarith
  have hu : μ ({ω | X ω = (1 : ℝ)} ∪ {ω | X ω = (-1 : ℝ)}) = 1 := by
    rw [measure_union hd hmn, hp, hn]
    exact ENNReal.add_halves 1
  rw [ae_iff]
  change μ ({ω | X ω = (1 : ℝ)} ∪ {ω | X ω = (-1 : ℝ)})ᶜ = 0
  rw [measure_compl (hmp.union hmn) (measure_ne_top _ _), hu]
  simp

private theorem rademacher_integrable {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (hm : Measurable X)
    (hs : ∀ᵐ ω ∂μ, X ω = 1 ∨ X ω = -1) : Integrable X μ := by
  apply Integrable.mono' (integrable_const (1 : ℝ)) hm.aestronglyMeasurable
  filter_upwards [hs] with ω hω
  rcases hω with h | h <;> simp [h]

private lemma rademacher_exp_integrable {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hm : Measurable X)
    (hs : ∀ᵐ ω ∂μ, X ω = 1 ∨ X ω = -1) (t : ℝ) :
    MeasureTheory.Integrable (fun ω => Real.exp (t * X ω)) μ := by
  apply (MeasureTheory.integrable_const (Real.exp |t|)).mono'
    ((Real.continuous_exp.measurable.comp (measurable_const.mul hm)).aestronglyMeasurable)
  filter_upwards [hs] with ω hω
  simp only [Function.comp_apply, Real.norm_eq_abs, Real.abs_exp]
  apply Real.exp_le_exp.mpr
  rcases hω with h | h
  · simpa [h] using le_abs_self t
  · simpa [h] using neg_le_abs t

/-- The two-sided tail bound for a finite Rademacher sum, with the
zero-variance right-hand side interpreted as zero. -/
theorem rademacher_sum_tail_bound
    {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (N : ℕ) (X : Fin N → Ω → ℝ) (a : Fin N → ℝ)
    (h_measurable : ∀ i : Fin N, Measurable (X i))
    (h_independent : ProbabilityTheory.iIndepFun X μ)
    (h_positive : ∀ i : Fin N,
      μ {ω : Ω | X i ω = (1 : ℝ)} = (1 / 2 : ENNReal))
    (h_negative : ∀ i : Fin N,
      μ {ω : Ω | X i ω = (-1 : ℝ)} = (1 / 2 : ENNReal))
    (t : ℝ) (ht : (0 : ℝ) < t) :
    (μ {ω : Ω |
      t ≤ |((∑ i : Fin N, a i * X i ω) : ℝ)|}).toReal ≤
      (if ((∑ i : Fin N, (a i) ^ (2 : ℕ)) : ℝ) = (0 : ℝ) then
        (0 : ℝ)
      else
        (2 : ℝ) * Real.exp
          (-(t ^ (2 : ℕ) /
            ((2 : ℝ) * ((∑ i : Fin N, (a i) ^ (2 : ℕ)) : ℝ))))) := by
  classical
  by_cases hv : ∑ i, (a i)^2 = 0
  · rw [if_pos hv]
    have hz := rademacher_zero_variance μ N X a hv t ht
    rw [hz]
  · rw [if_neg hv]
    have hs : ∀ i, ∀ᵐ ω ∂μ, X i ω = 1 ∨ X i ω = -1 :=
      fun i => rademacher_ae_sign μ (X i) (h_measurable i) (h_positive i) (h_negative i)
    have hi : ∀ i, Integrable (X i) μ :=
      fun i => rademacher_integrable μ (X i) (h_measurable i) (hs i)
    sorry
