import Mathlib.Probability.Distributions.Gaussian.Basic
import Mathlib.Probability.Distributions.Gaussian.Real

open MeasureTheory
open ProbabilityTheory

noncomputable section

namespace NormalDistribution

def normalDensity (μ : ℝ) (σ : ℝ) (x : ℝ) : ℝ :=
  (1 / (σ * Real.sqrt (2 * Real.pi))) *
    Real.exp (-((x - μ) ^ 2) / (2 * σ ^ 2))

def standardNormalDensity (x : ℝ) : ℝ :=
  (1 / Real.sqrt (2 * Real.pi)) * Real.exp (-(x ^ 2) / 2)

def Mean {Ω : Type*} [MeasurableSpace Ω]
    (X : Ω → ℝ) (P : Measure Ω) : ℝ :=
  ∫ ω, X ω ∂P

def Variance {Ω : Type*} [MeasurableSpace Ω]
    (X : Ω → ℝ) (P : Measure Ω) : ℝ :=
  ∫ ω, (X ω - Mean X P) ^ 2 ∂P

def HasDensity {Ω : Type*} [MeasurableSpace Ω]
    (X : Ω → ℝ) (P : Measure Ω) (f : ℝ → ℝ) : Prop :=
  Measure.map X P =
    Measure.withDensity volume (fun x : ℝ => ENNReal.ofReal (f x))

def IsStandardNormal {Ω : Type*} [MeasurableSpace Ω]
    (X : Ω → ℝ) (P : Measure Ω) : Prop :=
  Measurable X ∧
    HasDensity X P standardNormalDensity ∧
    Integrable X P ∧
    Integrable (fun ω => (X ω - (0 : ℝ)) ^ 2) P

def IsNormal {Ω : Type*} [MeasurableSpace Ω]
    (X : Ω → ℝ) (P : Measure Ω) (μ : ℝ) (σ : ℝ) : Prop :=
  Measurable X ∧
    0 < σ ∧
    ∃ Z : Ω → ℝ,
      Measurable Z ∧
      IsStandardNormal Z P ∧
      (∀ ω : Ω, X ω = μ + σ * Z ω) ∧
      HasDensity X P (normalDensity μ σ) ∧
      Integrable X P ∧
      Integrable (fun ω => (X ω - μ) ^ 2) P

theorem standard_normal_density
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → ℝ)
    (hX : IsStandardNormal X P) :
    ∀ x : ℝ,
      standardNormalDensity x =
        (1 / Real.sqrt (2 * Real.pi)) * Real.exp (-(x ^ 2) / 2) := by
  simp [standardNormalDensity]

theorem standard_normal_mean_zero
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → ℝ)
    (hX : IsStandardNormal X P) :
    Mean X P = (0 : ℝ) := by
  unfold Mean
  have hm : (∫ x : ℝ, x ∂ Measure.map X P) = (∫ ω : Ω, X ω ∂ P) := by
    simpa only [id_eq] using
      (MeasureTheory.integral_map hX.1.aemeasurable
        measurable_id.aestronglyMeasurable)
  rw [← hm, hX.2.1]
  have hd : (fun x : ℝ => ENNReal.ofReal (standardNormalDensity x)) =
      (fun x : ℝ => ProbabilityTheory.gaussianPDF 0 1 x) := by
    funext x
    simp [standardNormalDensity, ProbabilityTheory.gaussianPDF,
      ProbabilityTheory.gaussianPDFReal, ENNReal.ofReal_mul]
  rw [hd]
  have hg : ProbabilityTheory.gaussianReal 0 (1 : NNReal) =
      Measure.withDensity volume (fun x => ProbabilityTheory.gaussianPDF 0 1 x) := by
    simp [ProbabilityTheory.gaussianReal]
  rw [← hg]
  exact ProbabilityTheory.integral_id_gaussianReal (μ := (0 : ℝ)) (v := (1 : NNReal))

theorem standard_normal_variance_one
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → ℝ)
    (hX : IsStandardNormal X P) :
    Variance X P = (1 : ℝ) := by
  unfold Variance
  rw [standard_normal_mean_zero P X hX]
  simp only [sub_zero]
  have hm : (∫ x : ℝ, x ^ 2 ∂ Measure.map X P) =
      (∫ ω : Ω, X ω ^ 2 ∂ P) := by
    simpa using (MeasureTheory.integral_map hX.1.aemeasurable
      (by exact (measurable_id.pow_const 2).aestronglyMeasurable))
  rw [← hm, hX.2.1]
  have hd : (fun x : ℝ => ENNReal.ofReal (standardNormalDensity x)) =
      (fun x : ℝ => ProbabilityTheory.gaussianPDF 0 1 x) := by
    funext x
    simp [standardNormalDensity, ProbabilityTheory.gaussianPDF,
      ProbabilityTheory.gaussianPDFReal, ENNReal.ofReal_mul]
  rw [hd]
  have hg : ProbabilityTheory.gaussianReal 0 (1 : NNReal) =
      Measure.withDensity volume (fun x => ProbabilityTheory.gaussianPDF 0 1 x) := by
    simp [ProbabilityTheory.gaussianReal]
  rw [← hg]
  have hv := ProbabilityTheory.variance_fun_id_gaussianReal
    (μ := (0 : ℝ)) (v := (1 : NNReal))
  rw [ProbabilityTheory.variance_eq_integral measurable_id'.aemeasurable] at hv
  simpa using hv

theorem normal_density
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → ℝ) (μ : ℝ) (σ : ℝ)
    (hX : IsNormal X P μ σ) :
    ∀ x : ℝ,
      normalDensity μ σ x =
        (1 / (σ * Real.sqrt (2 * Real.pi))) *
          Real.exp (-((x - μ) ^ 2) / (2 * σ ^ 2)) := by
  simp [normalDensity]

theorem normal_mean
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → ℝ) (μ : ℝ) (σ : ℝ)
    (hX : IsNormal X P μ σ) :
    Mean X P = μ := by
  rcases hX with ⟨hXm, hσ, Z, hZm, hZstd, hrel, hdens, hXi, hXsq⟩
  have hmap : Measure.map Z P (Set.univ : Set ℝ) = P (Set.univ : Set Ω) := by
    simpa only [Set.preimage_univ] using
      (Measure.map_apply_of_aemeasurable (μ := P) (f := Z)
        hZm.aemeasurable (MeasurableSet.univ : MeasurableSet (Set.univ : Set ℝ)))
  have hP : P (Set.univ : Set Ω) = 1 := by
    calc
      P (Set.univ : Set Ω) = Measure.map Z P (Set.univ : Set ℝ) := hmap.symm
      _ = (Measure.withDensity volume
          (fun x : ℝ => ENNReal.ofReal (standardNormalDensity x)))
          (Set.univ : Set ℝ) := by rw [hZstd.2.1]
      _ = (ProbabilityTheory.gaussianReal 0 (1 : NNReal)) (Set.univ : Set ℝ) := by
        have hd : (fun x : ℝ => ENNReal.ofReal (standardNormalDensity x)) =
            (fun x : ℝ => ProbabilityTheory.gaussianPDF 0 1 x) := by
          funext x
          simp [standardNormalDensity, ProbabilityTheory.gaussianPDF,
            ProbabilityTheory.gaussianPDFReal, ENNReal.ofReal_mul]
        have hg : ProbabilityTheory.gaussianReal 0 (1 : NNReal) =
            Measure.withDensity volume (fun x => ProbabilityTheory.gaussianPDF 0 1 x) := by
          simp [ProbabilityTheory.gaussianReal]
        rw [hd, ← hg]
      _ = 1 := by simp [ProbabilityTheory.gaussianReal]
  letI : IsFiniteMeasure P := ⟨by simp [hP]⟩
  have hPreal : P.real (Set.univ : Set Ω) = 1 := by
    exact (ENNReal.toReal_eq_one_iff (P (Set.univ : Set Ω))).2 hP
  have hZint : Integrable Z P := hZstd.2.2.1
  have hconst : Integrable (fun _ : Ω => μ) P := integrable_const _
  have hscale : Integrable (fun ω => σ * Z ω) P := hZint.const_mul σ
  calc
    Mean X P = ∫ ω, μ + σ * Z ω ∂P := by
      unfold Mean
      exact integral_congr_ae (Filter.Eventually.of_forall hrel)
    _ = (∫ _ : Ω, μ ∂P) + ∫ ω, σ * Z ω ∂P := by
      exact integral_add hconst hscale
    _ = μ + σ * Mean Z P := by
      simp only [Mean, integral_const, integral_const_mul]
      rw [hPreal]
      simp only [one_smul]
    _ = μ + σ * (0 : ℝ) := by
      rw [standard_normal_mean_zero P Z hZstd]
    _ = μ := by ring

theorem normal_variance
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → ℝ) (μ : ℝ) (σ : ℝ)
    (hX : IsNormal X P μ σ) :
    Variance X P = σ ^ 2 := by
  rcases hX with ⟨hXm, hσ, Z, hZm, hZstd, hrel, hdens, hXi, hXsq⟩
  have hmean : Mean X P = μ := normal_mean P X μ σ
    ⟨hXm, hσ, Z, hZm, hZstd, hrel, hdens, hXi, hXsq⟩
  unfold Variance
  rw [hmean]
  have hfun : (fun ω : Ω => (X ω - μ) ^ 2) =
      (fun ω : Ω => (σ * Z ω) ^ 2) := by
    funext ω
    rw [hrel ω]
    ring
  rw [hfun]
  have hz : (∫ ω : Ω, Z ω ^ 2 ∂P) = (1 : ℝ) := by
    have hv := standard_normal_variance_one P Z hZstd
    unfold Variance at hv
    rw [standard_normal_mean_zero P Z hZstd] at hv
    simpa using hv
  calc
    (∫ ω, (σ * Z ω) ^ 2 ∂P) = σ ^ 2 * (∫ ω, Z ω ^ 2 ∂P) := by
      simp_rw [mul_pow]
      rw [← integral_const_mul]
    _ = σ ^ 2 := by rw [hz, mul_one]

end NormalDistribution
