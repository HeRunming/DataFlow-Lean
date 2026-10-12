import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Independence.Basic
import Mathlib.Data.Matrix.Basic

open MeasureTheory ProbabilityTheory

/-- A random matrix has independent standard normal entries. -/
def HasIndependentStandardNormalEntries
    {Ω : Type*} [MeasurableSpace Ω] {m n : ℕ}
    (G : Ω → Matrix (Fin m) (Fin n) ℝ) (P : Measure Ω) : Prop :=
  (∀ (i : Fin m) (j : Fin n),
    Measure.map (fun ω => G ω i j) P =
      ProbabilityTheory.gaussianReal (0 : ℝ) (1 : NNReal)) ∧
  ProbabilityTheory.iIndepFun
    (fun ij : Fin m × Fin n => fun ω => G ω ij.1 ij.2) P

/-- A random vector has the standard normal law coordinatewise with independent coordinates. -/
def HasStandardNormalVector
    {Ω : Type*} [MeasurableSpace Ω] {m : ℕ}
    (X : Ω → Fin m → ℝ) (P : Measure Ω) : Prop :=
  (∀ (i : Fin m),
    Measure.map (fun ω => X ω i) P =
      ProbabilityTheory.gaussianReal (0 : ℝ) (1 : NNReal)) ∧
  ProbabilityTheory.iIndepFun (fun i : Fin m => fun ω => X ω i) P

/-- Orthogonal unit vectors are mapped by an independent standard Gaussian matrix
    to independent standard Gaussian random vectors. -/
theorem gaussian_matrix_mulVec_independent
    {Ω : Type*} [MeasurableSpace Ω]
    {m n : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (G : Ω → Matrix (Fin m) (Fin n) ℝ)
    (u v : Fin n → ℝ)
    (hG : HasIndependentStandardNormalEntries G P)
    (hu : ((∑ i : Fin n, (u i) ^ 2) : ℝ) = (1 : ℝ))
    (hv : ((∑ i : Fin n, (v i) ^ 2) : ℝ) = (1 : ℝ))
    (huv : ((∑ i : Fin n, u i * v i) : ℝ) = (0 : ℝ)) :
    HasStandardNormalVector
        (fun ω => Matrix.mulVec (G ω) u) P ∧
      HasStandardNormalVector
        (fun ω => Matrix.mulVec (G ω) v) P ∧
        ProbabilityTheory.IndepFun
          (fun ω => Matrix.mulVec (G ω) u)
          (fun ω => Matrix.mulVec (G ω) v)
          P := by
  sorry
