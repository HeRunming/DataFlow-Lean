import Mathlib

open MeasureTheory

noncomputable section

namespace FairCoinTail

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A measurable real-valued Bernoulli random variable with parameter one half. -/
def FairBernoulli (μ : Measure Ω) (Y : Ω → ℝ) : Prop :=
  Measurable Y ∧
  (∀ᵐ ω ∂μ, Y ω = (0 : ℝ) ∨ Y ω = (1 : ℝ)) ∧
  μ {ω : Ω | Y ω = (0 : ℝ)} = (1 : ENNReal) / 2 ∧
  μ {ω : Ω | Y ω = (1 : ℝ)} = (1 : ENNReal) / 2

/-- A measurable real-valued symmetric Rademacher random variable. -/
def Rademacher (μ : Measure Ω) (X : Ω → ℝ) : Prop :=
  Measurable X ∧
  (∀ᵐ ω ∂μ, X ω = (-1 : ℝ) ∨ X ω = (1 : ℝ)) ∧
  μ {ω : Ω | X ω = (-1 : ℝ)} = (1 : ENNReal) / 2 ∧
  μ {ω : Ω | X ω = (1 : ℝ)} = (1 : ENNReal) / 2

/-- The number of heads, expressed as a real-valued sum of coin indicators. -/
def headsCount (N : ℕ) (Y : Fin N → Ω → ℝ) (ω : Ω) : ℝ :=
  Finset.sum (Finset.univ : Finset (Fin N)) (fun i : Fin N => Y i ω)

private lemma measurable_affine_two_sub_one
    (Y : Ω → ℝ) (hY : Measurable Y) :
    Measurable (fun ω : Ω => (2 : ℝ) * Y ω - (1 : ℝ)) := by
  exact (measurable_const.mul hY).sub measurable_const

theorem fairBernoulli_to_rademacher
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : Ω → ℝ) (hY : FairBernoulli μ Y) :
    Rademacher μ (fun ω : Ω => (2 : ℝ) * Y ω - (1 : ℝ)) := by
  rcases hY with ⟨hm, hr, h0, h1⟩
  refine ⟨measurable_affine_two_sub_one Y hm, ?_, ?_, ?_⟩
  · filter_upwards [hr] with ω hω
    rcases hω with hω | hω
    · left
      linarith
    · right
      linarith
  · have hs : {ω : Ω | (2 : ℝ) * Y ω - 1 = -1} = {ω | Y ω = 0} := by
      ext ω
      simp only [Set.mem_setOf_eq]
      constructor <;> intro h <;> linarith
    change μ {ω : Ω | (2 : ℝ) * Y ω - 1 = -1} = (1 : ENNReal) / 2
    rw [hs]
    exact h0
  · have hs : {ω : Ω | (2 : ℝ) * Y ω - 1 = 1} = {ω | Y ω = 1} := by
      ext ω
      simp only [Set.mem_setOf_eq]
      constructor <;> intro h <;> linarith
    change μ {ω : Ω | (2 : ℝ) * Y ω - 1 = 1} = (1 : ENNReal) / 2
    rw [hs]
    exact h1

theorem independent_coin_sum_to_rademacher_sum
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (N : ℕ) (Y : Fin N → Ω → ℝ)
    (hY : ∀ i : Fin N, FairBernoulli μ (Y i))
    (hIndependent : ProbabilityTheory.iIndepFun Y μ) :
    (∀ i : Fin N,
      Rademacher μ (fun ω : Ω => (2 : ℝ) * Y i ω - (1 : ℝ))) ∧
    ProbabilityTheory.iIndepFun
      (fun (i : Fin N) (ω : Ω) => (2 : ℝ) * Y i ω - (1 : ℝ)) μ ∧
    (∀ ω : Ω,
      (2 : ℝ) * headsCount N Y ω - (N : ℝ) =
        (Finset.sum (Finset.univ : Finset (Fin N))
          (fun i : Fin N => (2 : ℝ) * Y i ω - (1 : ℝ)) : ℝ)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    exact fairBernoulli_to_rademacher μ (Y i) (hY i)
  · let f : ℝ → ℝ := fun x => 2 * x - 1
    have hf : Measurable f := (measurable_const.mul measurable_id).sub measurable_const
    exact hIndependent.comp (fun _ => f) (fun _ => hf)
  · intro ω
    simp [headsCount, Finset.mul_sum]

private lemma rademacher_integral_zero
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ)
    (hX : Rademacher μ X) : ∫ ω, X ω ∂μ = 0 := by
  rcases hX with ⟨hmeas, hae, hneg, hpos⟩
  let A : Set Ω := {ω | X ω = 1}
  have hA : MeasurableSet A := hmeas (measurableSet_singleton (1 : ℝ))
  have hrep : X =ᵐ[μ] (fun ω => (-1 : ℝ) + 2 * Set.indicator A 1 ω) := by
    filter_upwards [hae] with ω hω
    rcases hω with hω | hω
    · simp [A, hω]
      norm_num
    · simp [A, hω]
      norm_num
  have hconst : Integrable (fun _ : Ω => (-1 : ℝ)) μ := integrable_const _
  have hind : Integrable (Set.indicator A (1 : Ω → ℝ)) μ :=
    Integrable.indicator (integrable_const (μ := μ) (c := (1 : ℝ))) hA
  rw [integral_congr_ae hrep, integral_add hconst (hind.const_mul 2)]
  rw [integral_const, integral_const_mul, integral_indicator hA]
  have hpos' : μ.real A = 1 / 2 := by
    change (μ A).toReal = 1 / 2
    rw [show A = {ω | X ω = 1} by rfl, hpos]
    norm_num
  simp [hpos']

private lemma exponent_normalization (N : ℕ) (hN : N ≠ 0) :
    -((N : ℝ) / 2) ^ 2 / (2 * (N : ℝ)) = -(N : ℝ) / 8 := by
  field_simp [show (N : ℝ) ≠ 0 by exact_mod_cast hN]
  ring

theorem probability_at_least_three_quarters_heads
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (N : ℕ) (Y : Fin N → Ω → ℝ)
    (hY : ∀ i : Fin N, FairBernoulli μ (Y i))
    (hIndependent : ProbabilityTheory.iIndepFun Y μ) :
    μ {ω : Ω | headsCount N Y ω ≥ ((3 : ℝ) / (4 : ℝ)) * (N : ℝ)} =
      μ {ω : Ω |
        (2 : ℝ) * headsCount N Y ω - (N : ℝ) ≥ (N : ℝ) / (2 : ℝ)} ∧
    μ {ω : Ω |
        (2 : ℝ) * headsCount N Y ω - (N : ℝ) ≥ (N : ℝ) / (2 : ℝ)} ≤
      ENNReal.ofReal (Real.exp (-(N : ℝ) / (8 : ℝ))) := by
  have hsum := independent_coin_sum_to_rademacher_sum (μ := μ) (N := N) (Y := Y) hY hIndependent
  constructor
  · congr 1
    ext ω
    simp only [Set.mem_setOf_eq]
    constructor <;> intro h <;> linarith
  ·
    by_cases hN : N = 0
    · subst N
      simp [headsCount]
    ·
      have hmgf : ∀ i : Fin N, ProbabilityTheory.HasSubgaussianMGF
          (fun ω => (2 : ℝ) * Y i ω - 1) 1 μ := by
        intro i
        have hi := ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
          (a := (-1 : ℝ)) (b := (1 : ℝ))
          (X := fun ω => (2 : ℝ) * Y i ω - 1) (μ := μ)
          (hsum.1 i).1.aemeasurable
          (by
            filter_upwards [(hsum.1 i).2.1] with ω hω
            rcases hω with hω | hω <;> simp [hω])
          (rademacher_integral_zero μ _ (hsum.1 i))
        convert hi using 1
        norm_num
      have hbound := ProbabilityTheory.HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun
        (μ := μ) (X := fun i : Fin N => fun ω => (2 : ℝ) * Y i ω - 1)
        hsum.2.1 (c := fun _ => 1) (s := Finset.univ)
        (by intro i hi; exact hmgf i)
        (ε := (N : ℝ) / 2) (by positivity)
      have hE : {ω : Ω | (N : ℝ) / 2 ≤ ∑ i : Fin N, ((2 : ℝ) * Y i ω - 1)} =
          {ω : Ω | (2 : ℝ) * headsCount N Y ω - (N : ℝ) ≥ (N : ℝ) / 2} := by
        ext ω
        simp only [Set.mem_setOf_eq]
        rw [← hsum.2.2 ω]
      rw [← hE]
      rw [← ENNReal.ofReal_toReal (measure_ne_top μ _)]
      apply ENNReal.ofReal_le_ofReal
      have hexp := exponent_normalization N hN
      simpa [MeasureTheory.Measure.real, hexp] using hbound

end FairCoinTail
