import Mathlib

namespace FateXWork.Environments.ItemsP218D1784C01EC

def minkowskiDifference {E : Type*} [Sub E] (T S : Set E) : Set E :=
  {z | ∃ x ∈ T, ∃ y ∈ S, z = x - y}

noncomputable def directionalWidth {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (θ : E) (T : Set E) : ℝ :=
  sSup ((fun p : E × E => inner ℝ θ (p.1 - p.2)) '' (T ×ˢ T))

/--
Source proof: The excerpt gives this equality as equation (7.16), after
rewriting pairwise differences as points of `T - T`.

Proof sketch: Unfold the two definitions and identify the two supremum sets.

Prover notes: The expectation and unit-sphere law in the source are omitted
because no probability space is specified in this source slice.
-/
theorem directionalWidth_eq_sSup_minkowskiDifference
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (θ : E) (T : Set E) :
    directionalWidth θ T =
      sSup ((fun z : E => inner ℝ θ z) '' minkowskiDifference T T) := by
  sorry

end FateXWork.Environments.ItemsP218D1784C01EC
