import Mathlib

noncomputable def lpNorm {n : ℕ} (p : ℝ) (x : Fin n → ℝ) : ℝ :=
  (∑ i, |x i| ^ p) ^ (1 / p)

/-- The unit ball associated with the finite-dimensional `ℓᵖ` expression above. -/
def lpUnitBall {n : ℕ} (p : ℝ) : Set (Fin n → ℝ) :=
  {x | lpNorm p x ≤ 1}

/--
Source: `HDP/source/environments.json:31-31`, equation (1.4). Source proof:
 the text refers to Exercise 1.17; no proof is supplied in the source. Prover
notes: use finite-dimensional power-mean/Hölder monotonicity for `0 < p ≤ q`.
Vectors in `ℝ^n` are represented by functions `Fin n → ℝ`.
-/
theorem lpNorm_mono_in_exponent
    {n : ℕ} (x : Fin n → ℝ) {p q : ℝ} (hp : 1 ≤ p) (hpq : p ≤ q) :
    lpNorm q x ≤ lpNorm p x := by sorry

/--
Source: `HDP/source/environments.json:31-31`, equation (1.4). Source proof:
 the inclusion is stated as the equivalent reformulation of the displayed
inequality, with the proof deferred to Exercise 1.17. Prover notes: unfold
`lpUnitBall` and apply `lpNorm_mono_in_exponent` to a member of the p-ball.
-/
theorem lpUnitBall_subset
    {n : ℕ} {p q : ℝ} (hp : 0 < p) (hpq : p ≤ q) :
    lpUnitBall (n := n) p ⊆ lpUnitBall (n := n) q := by sorry
