import Mathlib

/-!
# Finite-dimensional unit balls

This module formalizes the three examples in source item `p17.x2`, including
the two identities displayed as equation (1.3).
-/

namespace FateXWork.Environments.ItemsP17X28476E610

open Set

/-- The Euclidean unit ball in `ℝⁿ`, represented by a finite Euclidean space. -/
def euclideanUnitBall (n : ℕ) : Set (EuclideanSpace ℝ (Fin n)) :=
  Metric.closedBall 0 1

/-- The unit `ℓ∞` ball in the coordinate model `Fin n → ℝ`. -/
def infinityUnitBall (n : ℕ) : Set (Fin n → ℝ) :=
  {x | ∀ i, |x i| ≤ 1}

/-- The unit `ℓ¹` ball in the coordinate model `Fin n → ℝ`. -/
def oneUnitBall (n : ℕ) : Set (Fin n → ℝ) :=
  {x | ∑ i, |x i| ≤ 1}

/-- The positive and negative standard basis vectors of `ℝⁿ`. -/
def signedStandardBasis (n : ℕ) : Set (Fin n → ℝ) :=
  Set.range (fun i : Fin n => Pi.single i (1 : ℝ)) ∪
    Set.range (fun i : Fin n => -Pi.single i (1 : ℝ))

/-- Source `p17.x2`: `B₂ⁿ` is the closed Euclidean ball of radius one.

Source proof: the excerpt gives this as the meaning of the Euclidean unit ball and
contains no separate proof. Prover notes: unfold `euclideanUnitBall`. -/
theorem euclideanUnitBall_eq_closedBall (n : ℕ) :
    euclideanUnitBall n = Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 := by
  sorry

/-- Source `p17.x2`, equation (1.3): `B∞ⁿ = [-1,1]ⁿ`.

Source proof: no proof is included; the excerpt points generally to Exercise 1.6.
Prover notes: use set extensionality, unfold `infinityUnitBall` and `Set.Icc`,
and reduce coordinatewise to `|a| ≤ 1 ↔ -1 ≤ a ∧ a ≤ 1`. -/
theorem infinityUnitBall_eq_cube (n : ℕ) :
    infinityUnitBall n = Set.Icc (fun _ : Fin n => (-1 : ℝ)) (fun _ => (1 : ℝ)) := by
  sorry

/-- Source `p17.x2`, equation (1.3): the unit `ℓ¹` ball is the convex hull of
the signed standard basis vectors.

Source proof: the excerpt provides no proof and cites Exercise 1.6. Prover notes:
show the `ℓ¹` ball is convex and contains every signed basis vector for one
inclusion. For the reverse inclusion, decompose coordinates into positive and
negative parts; use a cancelling pair of signed basis vectors for any remaining
convex coefficient, and treat dimension zero separately. -/
theorem oneUnitBall_eq_convexHull_signedStandardBasis (n : ℕ) :
    oneUnitBall n = convexHull ℝ (signedStandardBasis n) := by
  sorry

end FateXWork.Environments.ItemsP17X28476E610
