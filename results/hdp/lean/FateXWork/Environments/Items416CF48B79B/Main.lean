import Mathlib

/-!
Source proof (HDP 4.16): choose the sign so that the inner product is nonnegative.
For unit vectors, the squared distance after this choice is `2 - 2 cos θ`, while
`sin² θ = 1 - cos² θ`; nonnegativity of `cos θ` gives the desired bound.
Prover notes: use the unit-norm inner-product expansion and
`InnerProductGeometry.inner_eq_cos_angle_of_norm_eq_one`, then compare squares
and conclude by square-root inequalities.
-/
theorem davis_kahan_angle_close_up_to_sign
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u v : E) (ε : ℝ)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hε : 0 < ε)
    (hacute : 0 ≤ inner ℝ u v)
    (hsin : Real.sin (InnerProductGeometry.angle u v) ≤ ε) :
    ∃ θ : ℝ, (θ = 1 ∨ θ = -1) ∧ ‖u - θ • v‖ ≤ Real.sqrt 2 * ε := by
  sorry
