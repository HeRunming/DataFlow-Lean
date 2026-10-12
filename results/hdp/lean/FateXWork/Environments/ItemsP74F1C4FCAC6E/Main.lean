import Mathlib

open scoped BigOperators

noncomputable section

namespace StandardNormalVector

/-- The law of a vector with independent standard normal coordinates. -/
def ZLaw (n : ℕ) : MeasureTheory.Measure (Fin n → ℝ) :=
  MeasureTheory.Measure.pi
    (fun (_i : Fin n) => ProbabilityTheory.gaussianReal (0 : ℝ) (1 : NNReal))

/-- The specified pointwise version of the density of the standard normal vector. -/
def fZ (n : ℕ) (z : Fin n → ℝ) : ℝ :=
  (∏ i : Fin n,
    ProbabilityTheory.gaussianPDFReal (0 : ℝ) (1 : NNReal) (z i) : ℝ)

/-- The square of the source's Euclidean norm, not the function-space supremum norm. -/
def euclideanNormSq (n : ℕ) (z : Fin n → ℝ) : ℝ :=
  (∑ i : Fin n, (z i) ^ (2 : ℕ) : ℝ)

/-- Equation (3.11), including the assertion that fZ is a density of Z. -/
theorem density_of_standard_normal_vector
    (n : ℕ) {Ω : Type*} [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) (Z : Ω → (Fin n → ℝ))
    (hZ : MeasureTheory.Measure.map Z P = ZLaw n) :
    MeasureTheory.Measure.map Z P =
        (MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ)).withDensity
          (fun z : Fin n → ℝ => ENNReal.ofReal (fZ n z)) ∧
      ∀ z : Fin n → ℝ,
        fZ n z =
            (∏ i : Fin n,
              ((1 : ℝ) / Real.sqrt ((2 : ℝ) * Real.pi)) *
                Real.exp (-((z i) ^ (2 : ℕ)) / (2 : ℝ)) : ℝ) ∧
        fZ n z =
            ((1 : ℝ) / (((2 : ℝ) * Real.pi) ^ ((n : ℝ) / (2 : ℝ)))) *
              Real.exp (-(euclideanNormSq n z) / (2 : ℝ)) := by sorry

end StandardNormalVector
