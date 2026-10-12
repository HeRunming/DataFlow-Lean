import Mathlib

open MeasureTheory
open ProbabilityTheory

namespace IsotropicRandomVector

noncomputable section

abbrev VectorSpace (n : ℕ) := EuclideanSpace ℝ (Fin n)

def projection {Ω : Type*} {n : ℕ} (X : Ω → VectorSpace n) (u : VectorSpace n) : Ω → ℝ :=
  fun x => inner ℝ (X x) u

def expected {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → ℝ) : ℝ :=
  ∫ x, f x ∂μ

def l2Norm {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → ℝ) : ℝ :=
  Real.sqrt (∫ x, (f x) ^ (2 : ℕ) ∂μ)

def Isotropic {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) (X : Ω → VectorSpace n) : Prop :=
  IsProbabilityMeasure μ ∧
    Measurable X ∧
    (∀ (u : VectorSpace n), Measurable (projection X u)) ∧
    (∀ (u : VectorSpace n), Integrable (projection X u) μ) ∧
    (∀ (u v : VectorSpace n),
      Integrable (fun x => projection X u x * projection X v x) μ) ∧
    (∀ (u : VectorSpace n), expected μ (projection X u) = (0 : ℝ)) ∧
    (∀ (u v : VectorSpace n),
      expected μ (fun x => projection X u x * projection X v x) = inner ℝ u v)

theorem isotropic_projection_expectation_and_l2
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) (X : Ω → VectorSpace n)
    (hX : Isotropic μ X)
    (u v : VectorSpace n) :
    expected μ (fun x => projection X u x * projection X v x) = inner ℝ u v ∧
      l2Norm μ (fun x => projection X u x - projection X v x) = ‖u - v‖ := by
  constructor
  · exact hX.2.2.2.2.2.2 u v
  · have h := hX.2.2.2.2.2.2 (u - v) (u - v)
    unfold l2Norm
    have hp : (fun x => (projection X u x - projection X v x) ^ (2 : ℕ)) =
        (fun x => projection X (u - v) x * projection X (u - v) x) := by
      funext x
      simp [projection, sub_eq_add_neg, inner_add_right, inner_neg_right]
      ring
    rw [hp]
    change Real.sqrt (expected μ (fun x => projection X (u - v) x * projection X (u - v) x)) = ‖u - v‖
    rw [h, real_inner_self_eq_norm_sq]
    exact Real.sqrt_sq_eq_abs _ |>.trans (abs_of_nonneg (norm_nonneg _))

end

end IsotropicRandomVector
