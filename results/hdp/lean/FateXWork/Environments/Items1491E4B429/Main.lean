import Mathlib

/--
Source proof: The inclusion `T ⊆ convexHull ℝ T` gives one inequality. For the
other, express a point of the convex hull as a finite convex combination and
use convexity to bound its value by a value attained on the original set.
Prover notes: Mathlib's `ConvexOn.exists_ge_of_mem_convexHull` and
`ConvexOn.bddAbove_convexHull` are likely useful for the supremum argument.
-/
theorem maximum_principle_on_convex_hull
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (f : E → ℝ) (hf : ConvexOn ℝ (Set.univ : Set E) f) (T : Set E) :
    sSup (f '' (convexHull ℝ T)) = sSup (f '' T) := by
  sorry
