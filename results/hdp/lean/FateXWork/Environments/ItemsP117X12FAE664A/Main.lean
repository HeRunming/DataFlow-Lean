import Mathlib

/--
Source proof: The source passage is an expository example rather than a proved
claim; no source proof is supplied.

Proof sketch: unfold the Euclidean metric on `EuclideanSpace` and use the
standard identification of distance with the norm of the difference.

Prover notes: This declaration formalizes equation (4.16). The surrounding
covering discussion is recorded as a scope change because it introduces no
formal covering predicate or assertion to prove in the source excerpt.
-/
theorem euclidean_distance_example (n : ℕ)
    (x y : EuclideanSpace ℝ (Fin n)) :
    dist x y = ‖x - y‖ := by
  sorry
