import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.Basic

open MeasureTheory ProbabilityTheory

noncomputable section

namespace GaussianVector

def IsStandardGaussianVector {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (X : Ω → Fin n → ℝ) (P : Measure Ω) : Prop :=
  ∀ coeff : Fin n → ℝ,
    Measure.map (fun ω => (∑ i : Fin n, coeff i * X ω i : ℝ)) P =
      ProbabilityTheory.gaussianReal 0
        (Real.toNNReal (∑ i : Fin n, (coeff i : ℝ) ^ 2))

private theorem independent_scalar_projections
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ}
    {X Y : Ω → Fin n → ℝ}
    (hX_meas : Measurable X) (hY_meas : Measurable Y)
    (hXY_indep : ProbabilityTheory.IndepFun X Y P)
    (a b : Fin n → ℝ) :
    ProbabilityTheory.IndepFun
      (fun ω => ∑ i, a i * X ω i)
      (fun ω => ∑ i, b i * Y ω i) P := by
  let f : (Fin n → ℝ) → ℝ := fun z => ∑ i, a i * z i
  let g : (Fin n → ℝ) → ℝ := fun z => ∑ i, b i * z i
  have hf : Measurable f := by fun_prop
  have hg : Measurable g := by fun_prop
  simpa [f, g, Function.comp_def] using hXY_indep.comp hf hg

private theorem transformed_gaussian_conclusion {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ}
    {X Y : Ω → Fin n → ℝ}
    (h_transform :
      ProbabilityTheory.IndepFun
          (fun ω i => (X ω i + Y ω i) / Real.sqrt (2 : ℝ))
          (fun ω i => (X ω i - Y ω i) / Real.sqrt (2 : ℝ)) P ∧
        IsStandardGaussianVector
          (fun ω i => (X ω i + Y ω i) / Real.sqrt (2 : ℝ)) P ∧
        IsStandardGaussianVector
          (fun ω i => (X ω i - Y ω i) / Real.sqrt (2 : ℝ)) P) :
    ProbabilityTheory.IndepFun
        (fun ω i => (X ω i + Y ω i) / Real.sqrt (2 : ℝ))
        (fun ω i => (X ω i - Y ω i) / Real.sqrt (2 : ℝ)) P ∧
      IsStandardGaussianVector
        (fun ω i => (X ω i + Y ω i) / Real.sqrt (2 : ℝ)) P ∧
      IsStandardGaussianVector
        (fun ω i => (X ω i - Y ω i) / Real.sqrt (2 : ℝ)) P := by
  exact h_transform

private theorem measurable_add_sub_transforms {Ω : Type*}
    [MeasurableSpace Ω] {n : ℕ}
    {X Y : Ω → Fin n → ℝ}
    (hX_meas : Measurable X) (hY_meas : Measurable Y) :
    Measurable (fun ω i => (X ω i + Y ω i) / Real.sqrt (2 : ℝ)) ∧
      Measurable (fun ω i => (X ω i - Y ω i) / Real.sqrt (2 : ℝ)) := by
  constructor <;> fun_prop

private theorem add_sub_transform_scalar_identity (x y a b : ℝ) :
    a * ((x + y) / Real.sqrt (2 : ℝ)) + b * ((x - y) / Real.sqrt (2 : ℝ)) =
      ((a + b) * x + (a - b) * y) / Real.sqrt (2 : ℝ) := by
  ring

theorem independent_standard_gaussian_vectors_add_sub {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ}
    {X Y : Ω → Fin n → ℝ}
    (hX_meas : Measurable X)
    (hY_meas : Measurable Y)
    (hXY_indep : ProbabilityTheory.IndepFun X Y P)
    (hX_gaussian : IsStandardGaussianVector X P)
    (hY_gaussian : IsStandardGaussianVector Y P) :
    ProbabilityTheory.IndepFun
        (fun ω i => (X ω i + Y ω i) / Real.sqrt (2 : ℝ))
        (fun ω i => (X ω i - Y ω i) / Real.sqrt (2 : ℝ)) P ∧
      IsStandardGaussianVector
        (fun ω i => (X ω i + Y ω i) / Real.sqrt (2 : ℝ)) P ∧
      IsStandardGaussianVector
        (fun ω i => (X ω i - Y ω i) / Real.sqrt (2 : ℝ)) P := by
  sorry

end GaussianVector
