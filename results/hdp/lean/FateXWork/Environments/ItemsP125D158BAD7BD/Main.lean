import Mathlib

namespace ItemsP125D158BAD7BD

/-- The unit sphere in the Euclidean space indexed by `Fin n`. -/
def unitSphere (n : ℕ) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | ‖x‖ = 1}

/--
Source proof: The source passage is an expository definition referring back to
Definition 4.1.8; no proof is supplied.

Proof sketch: This is a direct definition of the supremum of the Euclidean
norms of the matrix-vector products on the unit sphere. A later maximum
formulation can use compactness of the sphere and continuity of `A.mulVec`.

Prover notes: The source uses `max`; `sSup` is used here as the direct
order-theoretic representation, with attainment intentionally deferred.
-/
noncomputable def operatorNorm {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  sSup ((fun x : EuclideanSpace ℝ (Fin n) => ‖A.mulVec x‖) '' unitSphere n)

end ItemsP125D158BAD7BD
