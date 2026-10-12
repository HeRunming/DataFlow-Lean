import Mathlib

/-!
Formalization of the cube as the convex hull of its vertices.
-/

/--
Source proof: For each coordinate of `x`, use its position in `[-1, 1]` to
form the product weights of the two possible signs; these nonnegative weights
sum to one, and the resulting convex combination has coordinate `x i`.
Prover notes: The source's `[-1,1]^n` is represented by the pi-set of closed
intervals, and `{−1,1}^n` by functions whose coordinates are either `-1` or
`1`. The equality statement packages both the requested membership argument
and the easy reverse inclusion.
-/
theorem cube_eq_convexHull_vertices (n : ℕ) :
    Set.pi Set.univ (fun _ : Fin n => Set.Icc (-1 : ℝ) 1) =
      convexHull ℝ {v : Fin n → ℝ | ∀ i, v i = -1 ∨ v i = 1} := by
  sorry
