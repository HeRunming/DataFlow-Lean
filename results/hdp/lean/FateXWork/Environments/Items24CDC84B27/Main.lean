import Mathlib

open MeasureTheory ProbabilityTheory

namespace StandardNormalTailMoments

section

variable {Ω : Type*} [MeasurableSpace Ω]
variable (P : Measure Ω) [IsProbabilityMeasure P]
variable (g : Ω → ℝ) (hg : Measurable g)
variable (hnormal : Measure.map g P = ProbabilityTheory.gaussianReal (0 : ℝ) (1 : NNReal))

include hnormal hg

private theorem integral_comp_map_of_aemeasurable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (f : β → ℝ) (g : α → β) (hg : AEMeasurable g μ)
    (hf : AEStronglyMeasurable f (Measure.map g μ)) :
    ∫ x, f x ∂Measure.map g μ = ∫ a, f (g a) ∂μ := by
  exact MeasureTheory.integral_map hg hf

private theorem interval_exp_deriv (t b : ℝ) :
    ∫ x in t..b, -x * Real.exp (-(x ^ 2) / 2) =
      Real.exp (-(b ^ 2) / 2) - Real.exp (-(t ^ 2) / 2) := by
  apply intervalIntegral.integral_deriv_eq_sub'
  · funext x
    have hinner : HasDerivAt (fun y : ℝ => -(y ^ 2) / 2) (-x) x := by
      convert ((hasDerivAt_id x).pow 2).const_mul (-(2 : ℝ)⁻¹) using 1 <;> simp [id] <;> ring
    have hexp := (Real.hasDerivAt_exp (-(x ^ 2) / 2)).comp x hinner
    convert hexp.deriv using 1 <;> ring
  · intro x hx
    fun_prop
  · fun_prop

private theorem gaussian_tail_helper (t b : ℝ) (h : t ≤ b) :
    (∫ x in Set.Ioc t b, x * Real.exp (-(x ^ 2) / 2)) =
      ∫ x in t..b, x * Real.exp (-(x ^ 2) / 2) := by
  rw [intervalIntegral.integral_of_le h]

private theorem finite_gaussian_tail (t b : ℝ) (h : t ≤ b) :
    (∫ x in Set.Ioc t b, x * Real.exp (-(x ^ 2) / 2)) =
      Real.exp (-(t ^ 2) / 2) - Real.exp (-(b ^ 2) / 2) := by
  rw [gaussian_tail_helper (P := P) (g := g) (hg := hg) (hnormal := hnormal) t b h]
  have hi := interval_exp_deriv (P := P) (g := g) (hg := hg) (hnormal := hnormal) (t := t) (b := b)
  have hneg : (∫ x in t..b, -x * Real.exp (-(x ^ 2) / 2)) =
      -∫ x in t..b, x * Real.exp (-(x ^ 2) / 2) := by
    rw [← intervalIntegral.integral_neg]
    congr 1
    funext x
    ring
  rw [hneg] at hi
  linarith

private theorem interval_integral_add_adjacent (t b c : ℝ) (F : ℝ → ℝ)
    (h₁ : IntervalIntegrable F volume t b)
    (h₂ : IntervalIntegrable F volume b c) :
    (∫ x in t..c, F x) = (∫ x in t..b, F x) + ∫ x in b..c, F x := by
  symm
  exact intervalIntegral.integral_add_adjacent_intervals h₁ h₂

private theorem tail_integral_tendsto (t : ℝ) (F : ℝ → ℝ)
    (hF : IntegrableOn F (Set.Ioi t) volume) :
    Filter.Tendsto (fun b : ℝ => ∫ x in Set.Ioc t b, F x ∂volume)
      Filter.atTop (nhds (∫ x in Set.Ioi t, F x ∂volume)) := by
  have hu : (⋃ b : ℝ, Set.Ioc t b) = Set.Ioi t := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_Ioc]
    constructor
    · rintro ⟨b, htb, hxb⟩
      exact htb
    · intro htx
      exact ⟨x, htx, le_rfl⟩
  rw [← hu]
  apply tendsto_setIntegral_of_monotone (s := fun b : ℝ => Set.Ioc t b)
  · exact fun b => measurableSet_Ioc
  · intro b c hbc
    exact Set.Ioc_subset_Ioc_right hbc
  · simpa [hu] using hF

private theorem gaussian_density_bridge (F : ℝ → ℝ) :
    (∫ x, F x ∂(ProbabilityTheory.gaussianReal 0 (1 : NNReal))) =
      ∫ x, F x ∂(Measure.withDensity volume (ProbabilityTheory.gaussianPDF 0 1)) := by
  simp [ProbabilityTheory.gaussianReal]

private theorem gaussian_measure_eq :
    ProbabilityTheory.gaussianReal (0 : ℝ) (1 : NNReal) =
      Measure.withDensity volume (ProbabilityTheory.gaussianPDF 0 1) := by
  simp [ProbabilityTheory.gaussianReal]

/-- Part (a): the first truncated moment of a standard normal random variable. -/
theorem standard_normal_first_tail_moment
    (t : ℝ) (ht : 0 < t) :
    (∫ ω : Ω, g ω * (if g ω > t then (1 : ℝ) else (0 : ℝ)) ∂P) =
      (1 : ℝ) / Real.sqrt (2 * Real.pi) * Real.exp (-(t ^ 2) / 2) := by
  classical
  let f : ℝ → ℝ := fun x => x * (if x > t then (1 : ℝ) else 0)
  have hf : AEStronglyMeasurable f (Measure.map g P) := by
    apply (measurable_id.mul
      (Measurable.ite measurableSet_Ioi measurable_const measurable_const)).aestronglyMeasurable
  have hmap : (∫ x, f x ∂Measure.map g P) = ∫ ω, f (g ω) ∂P :=
    MeasureTheory.integral_map hg.aemeasurable hf
  rw [show (∫ ω, g ω * (if g ω > t then (1 : ℝ) else 0) ∂P) = ∫ ω, f (g ω) ∂P by simp [f]]
  rw [← hmap, hnormal]
  sorry

/-- Part (b): the second truncated moment bound, quantified over all real thresholds as in the source. -/
theorem standard_normal_second_tail_moment_bound
    (t : ℝ) :
    (∫ ω : Ω, (g ω) ^ 2 * (if g ω > t then (1 : ℝ) else (0 : ℝ)) ∂P) ≤
      (t + (1 : ℝ) / t) *
        ((1 : ℝ) / Real.sqrt (2 * Real.pi) * Real.exp (-(t ^ 2) / 2)) := by
  sorry

end

end StandardNormalTailMoments
