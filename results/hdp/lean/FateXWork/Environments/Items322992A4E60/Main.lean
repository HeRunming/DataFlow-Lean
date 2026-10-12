import Mathlib

open MeasureTheory ProbabilityTheory

namespace StandardNormalDirection

noncomputable def l2Norm {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  Real.sqrt (∑ i : Fin n, (x i) ^ 2 : ℝ)

def IsStandardNormalVector {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (g : Ω → Fin n → ℝ) (μ : Measure Ω) : Prop :=
  (∀ i : Fin n,
    Measure.map (fun ω : Ω => g ω i) μ =
      ProbabilityTheory.gaussianReal (0 : ℝ) (1 : NNReal)) ∧
    ProbabilityTheory.iIndepFun (fun i : Fin n => fun ω : Ω => g ω i) μ

private theorem measurable_l2Norm_map
    {n : ℕ} : Measurable (fun x : Fin n → ℝ => l2Norm x) := by
  unfold l2Norm
  measurability

private theorem standard_normal_coordinate_maps
    {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (μ : Measure Ω) (g : Ω → Fin n → ℝ)
    (hstandard : IsStandardNormalVector g μ) :
    ∀ i : Fin n, Measure.map (fun ω => g ω i) μ = ProbabilityTheory.gaussianReal 0 1 := by
  exact hstandard.1

private theorem standard_normal_probability_measure
    {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (μ : Measure Ω) (g : Ω → Fin n → ℝ)
    (hg : Measurable g) (hstandard : IsStandardNormalVector g μ) : μ Set.univ = 1 := by
  unfold IsStandardNormalVector at hstandard
  let i : Fin n := ⟨0, hn⟩
  have hm := Measure.map_apply_of_aemeasurable (μ := μ)
    ((measurable_pi_apply i).comp hg).aemeasurable MeasurableSet.univ
  have hu : Measure.map (fun ω : Ω => g ω i) μ Set.univ = μ Set.univ := by
    simpa using hm
  rw [← hu, hstandard.1 i]
  simp

private theorem measurable_normal_direction
    {n : ℕ} :
    Measurable (fun x : Fin n → ℝ => fun i : Fin n => x i / l2Norm x) := by
  unfold l2Norm
  measurability

private theorem measurable_norm_and_direction
    {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (g : Ω → Fin n → ℝ) (hg : Measurable g) :
    Measurable (fun ω : Ω => l2Norm (g ω)) ∧
      Measurable (fun ω : Ω => fun i : Fin n => g ω i / l2Norm (g ω)) := by
  exact ⟨measurable_l2Norm_map.comp hg, measurable_normal_direction.comp hg⟩

private theorem l2Norm_nonnegative
    {n : ℕ} (x : Fin n → ℝ) : 0 ≤ l2Norm x := by
  unfold l2Norm
  positivity

private theorem norm_direction_measurable_helper
    {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (g : Ω → Fin n → ℝ) (hg : Measurable g) :
    Measurable (fun ω : Ω => fun i : Fin n => g ω i / l2Norm (g ω)) := by
  exact (measurable_norm_and_direction g hg).2

private theorem radial_direction_independence_transport
    {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} {μ : Measure Ω} {g : Ω → Fin n → ℝ}
    (hpolar : ProbabilityTheory.IndepFun
      (fun ω : Ω => l2Norm (g ω))
      (fun ω : Ω => fun i : Fin n => g ω i / l2Norm (g ω))
      μ) :
    ProbabilityTheory.IndepFun
      (fun ω : Ω => l2Norm (g ω))
      (fun ω : Ω => fun i : Fin n => g ω i / l2Norm (g ω))
      μ := hpolar

theorem standard_normal_norm_direction_independent
    {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n)
    (μ : Measure Ω)
    (g : Ω → Fin n → ℝ)
    (hg : Measurable g)
    (hstandard : IsStandardNormalVector g μ) :
    ProbabilityTheory.IndepFun
      (fun ω : Ω => l2Norm (g ω))
      (fun ω : Ω => fun i : Fin n => g ω i / l2Norm (g ω))
      μ := by
  classical
  have hmeas := measurable_norm_and_direction g hg
  have hμ : μ Set.univ = 1 := standard_normal_probability_measure hn μ g hg hstandard
  have hnonneg : ∀ ω : Ω, 0 ≤ l2Norm (g ω) := fun ω => l2Norm_nonnegative (g ω)
  sorry

end StandardNormalDirection
