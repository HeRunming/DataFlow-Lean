import Mathlib

/-!
Source: HDP/source/environments.json, item p94.f1 (Lemma 3.7.4).

The source's tensor-power construction is represented by coordinate functions on
`k`-tuples of indices. This is an explicit finite-dimensional model of the
claimed feature space; the inner-product identity is left for the proving pass.
-/

open scoped BigOperators

namespace FateXWork.Environments.ItemsP94F16EDCCC6E

def TensorSpace (n k : ℕ) := (Fin k → Fin n) → ℝ

def tensorLift {n k : ℕ} (u : Fin n → ℝ) : TensorSpace n k :=
  fun I => ∏ j, u (I j)

def tensorInner {n k : ℕ} (x y : TensorSpace n k) : ℝ :=
  ∑ I, x I * y I

def vectorInner {n : ℕ} (u v : Fin n → ℝ) : ℝ :=
  ∑ i, u i * v i

/-!
The existential feature-map formulation in the source is recorded separately:
the chosen feature space is `TensorSpace n k` and the witnessing map is
`tensorLift`.  The coordinate model is the intentional replacement for the
source's abstract Hilbert-space presentation.
-/
theorem tensor_feature_map_exists (n k : ℕ) :
    ∃ Φ : (Fin n → ℝ) → TensorSpace n k,
      ∀ u v, tensorInner (Φ u) (Φ v) = vectorInner u v ^ k := by
  sorry

/-!
Source proof: the source identifies the feature map with the `k`-fold tensor
power `u ^⊗ k`; expanding the coordinatewise product and finite sums gives
the stated identity. Prover notes: use finite-sum/product algebra, with
`Finset.prod_univ` and `Finset.sum_univ`; the coordinate model is recorded in
the definitions above.
-/
theorem tensorInner_tensorLift_eq_pow (n k : ℕ) (u v : Fin n → ℝ) :
    tensorInner (n := n) (k := k) (tensorLift u) (tensorLift v) = vectorInner u v ^ k := by
  sorry

end FateXWork.Environments.ItemsP94F16EDCCC6E
