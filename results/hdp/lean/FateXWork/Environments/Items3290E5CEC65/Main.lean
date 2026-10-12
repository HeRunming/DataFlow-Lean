import Mathlib

open scoped BigOperators

namespace ParsevalFrame

def dotProduct {n : Nat} (x y : Fin n → ℝ) : ℝ :=
  ∑ j : Fin n, x j * y j

def IsParsevalFrame {n N : Nat} (u : Fin N → Fin n → ℝ) : Prop :=
  ∀ x : Fin n → ℝ,
    (∑ i : Fin N, (dotProduct x (u i)) ^ (2 : Nat)) =
      ∑ j : Fin n, x j ^ (2 : Nat)

def HasOrthonormalRows {n N : Nat} (A : Matrix (Fin n) (Fin N) ℝ) : Prop :=
  ∀ j k : Fin n,
    dotProduct (A j) (A k) = if j = k then (1 : ℝ) else (0 : ℝ)

theorem parsevalFrame_iff_orthonormalRows
    {n N : Nat} (u : Fin N → Fin n → ℝ) :
    IsParsevalFrame u ↔
      HasOrthonormalRows
        (let A : Matrix (Fin n) (Fin N) ℝ := fun j i => u i j
         A) := by
  classical
  change (∀ x : Fin n → ℝ, (∑ i : Fin N, (∑ j : Fin n, x j * u i j) ^ 2) = ∑ j : Fin n, x j ^ 2) ↔
    ∀ j k : Fin n, (∑ i : Fin N, u i j * u i k) = if j = k then 1 else 0
  constructor
  · intro h j k
    by_cases e : j = k
    · subst k
      have hv := h (Pi.single j 1)
      have hv' : (∑ i : Fin N, u i j ^ 2) = 1 := by
        simpa [Pi.single_apply, pow_two] using hv
      simpa [pow_two] using hv'
    · let v : Fin n → ℝ := Pi.single j 1 + Pi.single k 1
      have hs (i : Fin N) : (∑ l : Fin n, v l * u i l) = u i j + u i k := by
        simp only [v, Pi.add_apply]
        simp_rw [add_mul]
        rw [Finset.sum_add_distrib]
        simp [Pi.single_apply]
      have hrv (l : Fin n) : v l ^ 2 = (if l = j then 1 else 0) + (if l = k then 1 else 0) := by
        have kneqj : k ≠ j := Ne.symm e
        by_cases lj : l = j <;> by_cases lk : l = k <;> simp [v, Pi.add_apply, lj, lk, e, kneqj]
      have hr : (∑ l : Fin n, v l ^ 2) = 2 := by
        simp_rw [hrv]
        rw [Finset.sum_add_distrib]
        simp [Finset.sum_ite_eq']
        norm_num
      have hv := h v
      have hv' : (∑ i : Fin N, (u i j + u i k) ^ 2) = 2 := by
        calc
          _ = ∑ i : Fin N, (∑ l : Fin n, v l * u i l) ^ 2 := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [hs]
          _ = ∑ l : Fin n, v l ^ 2 := hv
          _ = 2 := hr
      have hj' : (∑ i : Fin N, u i j ^ 2) = 1 := by
        simpa [Pi.single_apply, pow_two] using h (Pi.single j 1)
      have hk' : (∑ i : Fin N, u i k ^ 2) = 1 := by
        simpa [Pi.single_apply, pow_two] using h (Pi.single k 1)
      have hexpand : (∑ i : Fin N, (u i j + u i k) ^ 2) =
          (∑ i : Fin N, u i j ^ 2) + (∑ i : Fin N, u i k ^ 2) +
            (∑ i : Fin N, u i j * u i k) + (∑ i : Fin N, u i k * u i j) := by
        rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      rw [hexpand] at hv'
      have hcross : (∑ i : Fin N, u i j * u i k) + (∑ i : Fin N, u i k * u i j) = 0 := by
        linarith
      have hsymm : (∑ i : Fin N, u i k * u i j) = ∑ i : Fin N, u i j * u i k := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      rw [if_neg e]
      rw [hsymm] at hcross
      linarith
  · intro h x
    simp only [pow_two]
    calc
      (∑ i : Fin N, (∑ j : Fin n, x j * u i j) * (∑ k : Fin n, x k * u i k)) =
          ∑ i : Fin N, ∑ j : Fin n, ∑ k : Fin n, (x j * u i j) * (x k * u i k) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j hj
        rw [Finset.mul_sum]
      _ = ∑ j : Fin n, ∑ k : Fin n, x j * x k * (∑ i : Fin N, u i j * u i k) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j hj
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro k hk
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = ∑ j : Fin n, x j * x j := by
        simp_rw [h]
        simp

end ParsevalFrame
