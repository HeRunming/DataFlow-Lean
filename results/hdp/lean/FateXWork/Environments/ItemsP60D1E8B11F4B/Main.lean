import Mathlib

namespace LaplaceStatement

noncomputable def laplacePDF (μ x : ℝ) : ℝ :=
  (1 / (2 : ℝ)) * Real.exp (-(|x - μ|))

theorem laplacePDF_integrable (μ : ℝ) :
    MeasureTheory.Integrable
        (fun x : ℝ => laplacePDF μ x)
        (MeasureTheory.volume : MeasureTheory.Measure ℝ) ∧
      ((∫ x : ℝ, laplacePDF μ x ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ)) : ℝ) = (1 : ℝ) := by
  sorry

theorem laplace_mean (μ : ℝ) :
    MeasureTheory.Integrable
        (fun x : ℝ => x * laplacePDF μ x)
        (MeasureTheory.volume : MeasureTheory.Measure ℝ) ∧
      ((∫ x : ℝ, x * laplacePDF μ x ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ)) : ℝ) = μ := by
  sorry

theorem laplace_variance (μ : ℝ) :
    MeasureTheory.Integrable
        (fun x : ℝ => (x - μ) ^ (2 : ℕ) * laplacePDF μ x)
        (MeasureTheory.volume : MeasureTheory.Measure ℝ) ∧
      ((∫ x : ℝ, (x - μ) ^ (2 : ℕ) * laplacePDF μ x ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ)) : ℝ) = (2 : ℝ) := by
  sorry

end LaplaceStatement
