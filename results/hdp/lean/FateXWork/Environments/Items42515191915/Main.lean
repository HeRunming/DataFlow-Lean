import Mathlib

/-!
Formalization of source item 4.2.5, "Packing balls into K".
-/

/-- A set is ε-separated when distinct points have distance strictly larger than ε. -/
def EpsilonSeparated {α : Type*} [PseudoMetricSpace α] (N : Set α) (ε : ℝ) : Prop :=
  ∀ ⦃x⦄, x ∈ N → ∀ ⦃y⦄, y ∈ N → x ≠ y → ε < dist x y

/--
Source proof: if two closed ε/2-balls centered at distinct points intersect,
choose a common point and apply the triangle inequality to obtain
`dist x y ≤ ε`, contradicting ε-separation.
Prover notes: unfold `EpsilonSeparated`; prove pairwise disjointness by
contradiction and use the two closed-ball membership inequalities together
with `dist_triangle`.
-/
theorem closedBall_half_pairwiseDisjoint
    {α : Type*} [PseudoMetricSpace α] {N : Set α} {ε : ℝ}
    (hN : EpsilonSeparated N ε) :
    Set.PairwiseDisjoint N (fun x => Metric.closedBall x (ε / 2)) := by
  sorry
