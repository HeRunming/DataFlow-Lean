import Mathlib

namespace Items418F0256182

/-!
Formalization of Definition 4.1.8 from HDP/source/environments.json.
-/

/--
The operator norm of a real matrix, presented as the infimum of the constants
which bound its Euclidean action on every vector.

Source proof: This source entry is a definition; no proof is supplied.
Proof sketch: The displayed characterization is the defining least-bound
formulation. Prover notes: the equivalence with the maximum formulations in
(4.9) is intentionally not asserted here, since it requires finite-dimensional
compactness and a separate statement review.
-/
noncomputable def operatorNorm {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℝ) : ℝ :=
  sInf {K : ℝ | ∀ x : n → ℝ, ‖Matrix.mulVec A x‖ ≤ K * ‖x‖}

end Items418F0256182
