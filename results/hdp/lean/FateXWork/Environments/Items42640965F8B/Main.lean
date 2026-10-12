import Mathlib

open Set

namespace EpsilonNet

variable {X : Type*} [MetricSpace X]

def IsEpsilonSeparated (epsilon : NNReal) (S : Set X) : Prop :=
  ∀ ⦃x : X⦄, x ∈ S → ∀ ⦃y : X⦄, y ∈ S → x ≠ y → (epsilon : ℝ) < dist x y

def IsEpsilonNet (epsilon : NNReal) (K N : Set X) : Prop :=
  ∀ ⦃x : X⦄, x ∈ K → ∃ n : X, n ∈ N ∧ dist x n ≤ (epsilon : ℝ)

private lemma insert_epsilonSeparated_of_forall_dist
    (epsilon : NNReal) (x : X) (N : Set X)
    (hNsep : IsEpsilonSeparated epsilon N)
    (hnot : ∀ n, n ∈ N → (epsilon : ℝ) < dist x n) :
    IsEpsilonSeparated epsilon (insert x N) := by
  intro a ha b hb hab
  rcases Set.mem_insert_iff.mp ha with ha | ha
  · have ha_eq : a = x := ha
    rcases Set.mem_insert_iff.mp hb with hb | hb
    · have hb_eq : b = x := hb
      subst a
      subst b
      exact (hab rfl).elim
    · subst a
      exact hnot b hb
  · rcases Set.mem_insert_iff.mp hb with hb | hb
    · have hb_eq : b = x := hb
      subst b
      simpa only [dist_comm] using hnot a ha
    · exact hNsep ha hb hab

theorem maximal_epsilonSeparated_is_epsilonNet
    (epsilon : NNReal) (K N : Set X)
    (hNK : N ⊆ K)
    (hNsep : IsEpsilonSeparated epsilon N)
    (hNmax : ∀ S : Set X, N ⊆ S → S ⊆ K → IsEpsilonSeparated epsilon S → S ⊆ N) :
    IsEpsilonNet epsilon K N := by
  classical
  intro x hxK
  by_cases hxN : x ∈ N
  · refine ⟨x, hxN, ?_⟩
    simpa only [dist_self] using
      (show (0 : ℝ) ≤ (epsilon : ℝ) by positivity)
  · by_contra hcontra
    have hnot : ∀ n, n ∈ N → (epsilon : ℝ) < dist x n := by
      intro n hn
      apply lt_of_not_ge
      intro hle
      exact hcontra ⟨n, hn, hle⟩
    have hNsub : N ⊆ insert x N := by
      intro n hn
      exact Set.mem_insert_iff.mpr (Or.inr hn)
    have hKsub : insert x N ⊆ K := by
      intro y hy
      rcases Set.mem_insert_iff.mp hy with hy | hy
      · have hy_eq : y = x := hy
        subst y
        exact hxK
      · exact hNK hy
    have hSep : IsEpsilonSeparated epsilon (insert x N) :=
      insert_epsilonSeparated_of_forall_dist epsilon x N hNsep hnot
    have hmax : insert x N ⊆ N := hNmax (insert x N) hNsub hKsub hSep
    exact hxN (hmax (Set.mem_insert_iff.mpr (Or.inl rfl)))

end EpsilonNet
