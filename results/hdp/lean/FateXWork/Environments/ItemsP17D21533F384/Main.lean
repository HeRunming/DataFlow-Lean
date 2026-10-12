import Mathlib

namespace ItemsP17D21533F384

/-- The finite-dimensional ℓ^p norm on `ℝ^n` for `1 ≤ p`. -/
noncomputable def lpNorm {n : ℕ} (p : ℝ) (hp : 1 ≤ p) (x : Fin n → ℝ) : ℝ :=
  (∑ i, |x i| ^ p) ^ (1 / p)

/-- The unit ball of the ℓ^p norm on `ℝ^n`. -/
def unitBall {n : ℕ} (p : ℝ) (hp : 1 ≤ p) : Set (Fin n → ℝ) :=
  {x | lpNorm p hp x ≤ 1}

/-- Characterization of the ℓ^p unit ball as the set of vectors of norm at most one. -/
theorem unitBall_eq_setOf {n : ℕ} (p : ℝ) (hp : 1 ≤ p) :
    unitBall p hp = {x : Fin n → ℝ | lpNorm p hp x ≤ 1} := by
  ext x
  rfl

end ItemsP17D21533F384
