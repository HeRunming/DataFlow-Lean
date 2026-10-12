import Mathlib

/-!
Formalization of source item `p286.a1`, equation (9.23).

Source proof: the source presents the recovery program and states, without a
formal derivation, that its feasible region is convex and computationally
tractable. The convexity assertion below records the mathematically precise
part of that claim; computational tractability is documented as an intentional
scope change in the blueprint because it is not a proposition supplied with a
computational model here.

Prover notes: prove the feasible set is the intersection of the affine fiber of `A.mulVec` at `y` and the sublevel set of the ℓ¹ norm. Use convexity of affine preimages and norm sublevel sets (or unfold `Convex` and combine linearity with the triangle inequality).
-/
theorem recovery_program_feasible_set_convex
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (y : Fin m → ℝ) (s : ℝ) :
    Convex ℝ {x : Fin n → ℝ |
      (A.mulVec x = y) ∧ (∑ i, ‖x i‖) ≤ Real.sqrt s} := by
  sorry
