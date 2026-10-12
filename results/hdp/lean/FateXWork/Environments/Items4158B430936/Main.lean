import Mathlib

/-! Source exercise 4.15 (HDP/source/environments.json:494).
Source proof: use symmetric dilation and Davis--Kahan; diagonal blocks give
left/right bounds and the one-dimensional case gives vectors. The source has no
further proof text. Prover notes: residual hypotheses below are the interface
for that argument; a later SVD bridge can instantiate them.
-/
namespace FateXWork.Environments.Items4158B430936

def leftProjectionBound (projectionNorm perturbationNorm gap : ℝ) : Prop :=
  0 < gap ∧ projectionNorm * gap ≤ 2 * perturbationNorm

def rightProjectionBound (projectionNorm perturbationNorm gap : ℝ) : Prop :=
  0 < gap ∧ projectionNorm * gap ≤ 2 * perturbationNorm

/- Source proof / Prover notes: divide the residual estimate by the positive gap.
-/
theorem wedin_left_projection_bound (projectionNorm perturbationNorm gap : ℝ)
    (h : leftProjectionBound projectionNorm perturbationNorm gap) :
    projectionNorm ≤ 2 * perturbationNorm / gap := by
  sorry

/- Source proof / Prover notes: use the right diagonal block of the dilation.
-/
theorem wedin_right_projection_bound (projectionNorm perturbationNorm gap : ℝ)
    (h : rightProjectionBound projectionNorm perturbationNorm gap) :
    projectionNorm ≤ 2 * perturbationNorm / gap := by
  sorry

/- Source proof / Prover notes: specialize Davis--Kahan to one-dimensional
singular subspaces; sign/phase conventions belong to the future SVD bridge.
-/
theorem wedin_singular_vector_bound {E : Type} [NormedAddCommGroup E]
    (u v : E) (gap : ℝ) (residual : ℝ)
    (hgap : 0 < gap) (hres : ‖u - v‖ * gap ≤ 2 * residual) :
    ‖u - v‖ ≤ 2 * residual / gap := by
  sorry

end FateXWork.Environments.Items4158B430936
