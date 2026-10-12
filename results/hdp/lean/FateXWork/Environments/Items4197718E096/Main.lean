import Mathlib

/-!
Source proof / Prover notes: Remark 4.1.9 is a definition-level
 generalization rather than a theorem with a proof. Replacing the particular
 ℓ² sizes by arbitrary domain and codomain size functions yields the intended
 generalized operator-norm construction; Exercises 4.18–4.22 supply examples
 and properties.
-/

noncomputable def generalizedOperatorNorm {E F : Type*}
    (domainSize : E → ℝ) (codomainSize : F → ℝ) (f : E → F) : ℝ :=
  sInf {c : ℝ | 0 ≤ c ∧ ∀ x, codomainSize (f x) ≤ c * domainSize x}
