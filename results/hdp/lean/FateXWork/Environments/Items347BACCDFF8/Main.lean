import Mathlib

open scoped BigOperators

namespace MatrixSignBilinear

variable {m n : ℕ}

abbrev Vector (k : ℕ) := Fin k → ℝ

local notation "⟪" x "," A "," y "⟫" =>
  ∑ i : Fin m, ∑ j : Fin n, y i * A i j * x j

def InCube {k : ℕ} (x : Vector k) : Prop :=
  ∀ i : Fin k, (-1 : ℝ) ≤ x i ∧ x i ≤ (1 : ℝ)

def SignVector {k : ℕ} (x : Vector k) : Prop :=
  ∀ i : Fin k, x i = (-1 : ℝ) ∨ x i = (1 : ℝ)

noncomputable def infNorm {k : ℕ} (x : Vector k) : ℝ :=
  sSup (Set.range (fun i : Fin k => |x i|))

def PropertyA (A : Matrix (Fin m) (Fin n) ℝ) : Prop :=
  ∀ x : Vector n, SignVector x →
    ∀ y : Vector m, SignVector y →
      ⟪x, A, y⟫ ≤ (1 : ℝ)

def PropertyB (A : Matrix (Fin m) (Fin n) ℝ) : Prop :=
  ∀ x : Vector n, InCube x →
    ∀ y : Vector m, InCube y →
      ⟪x, A, y⟫ ≤ (1 : ℝ)

def PropertyC (A : Matrix (Fin m) (Fin n) ℝ) : Prop :=
  ∀ x : Vector n, ∀ y : Vector m,
    ⟪x, A, y⟫ ≤ infNorm x * infNorm y

def PropertyAAbs (A : Matrix (Fin m) (Fin n) ℝ) : Prop :=
  ∀ x : Vector n, SignVector x →
    ∀ y : Vector m, SignVector y →
      |⟪x, A, y⟫| ≤ (1 : ℝ)

def PropertyBAbs (A : Matrix (Fin m) (Fin n) ℝ) : Prop :=
  ∀ x : Vector n, InCube x →
    ∀ y : Vector m, InCube y →
      |⟪x, A, y⟫| ≤ (1 : ℝ)

def PropertyCAbs (A : Matrix (Fin m) (Fin n) ℝ) : Prop :=
  ∀ x : Vector n, ∀ y : Vector m,
    |⟪x, A, y⟫| ≤ infNorm x * infNorm y

private lemma linear_cube_bound {k : ℕ} (c x : Vector k) (hx : InCube x)
    (h : ∀ s : Vector k, SignVector s → (∑ i : Fin k, c i * s i) ≤ 1) :
    (∑ i : Fin k, c i * x i) ≤ 1 := by
  let s : Vector k := fun i => if 0 ≤ c i then 1 else -1
  have hs : SignVector s := by
    intro i
    by_cases hc : 0 ≤ c i <;> simp [s, hc]
  calc
    (∑ i : Fin k, c i * x i) ≤ ∑ i : Fin k, c i * s i := by
      apply Finset.sum_le_sum
      intro i hi
      dsimp [s]
      by_cases hc : 0 ≤ c i
      · rw [if_pos hc]
        nlinarith [ (hx i).1, (hx i).2 ]
      · rw [if_neg hc]
        nlinarith [ (hx i).1, (hx i).2 ]
    _ ≤ 1 := h s hs

private lemma infNorm_nonneg {k : ℕ} (x : Vector k) : 0 ≤ infNorm x := by
  by_cases hk : Nonempty (Fin k)
  · let i : Fin k := Classical.choice hk
    unfold infNorm
    have hi : |x i| ∈ Set.range (fun j : Fin k => |x j|) := ⟨i, rfl⟩
    have hle := le_csSup (Set.finite_range (fun j : Fin k => |x j|)).bddAbove hi
    linarith [abs_nonneg (x i)]
  · have he : IsEmpty (Fin k) := not_nonempty_iff.mp hk
    letI := he
    change (0 : ℝ) ≤ sSup (Set.range (fun i : Fin k => |x i|))
    rw [Set.range_eq_empty]
    norm_num

private theorem leanflow_equivalent_properties_sign_in_cube {k : ℕ} {z : Vector k} (hz : SignVector z) : InCube z := by
  intro i
  rcases hz i with h | h
  · constructor <;> nlinarith [h]
  · constructor <;> nlinarith [h]

private lemma sum_sum_mul_right {α β : Type*} [Fintype α] [Fintype β] {R : Type*} [CommSemiring R]
    (c : α → β → R) (t : β → R) :
    (∑ i : α, ∑ j : β, c i j * t j) =
      ∑ j : β, (∑ i : α, c i j) * t j := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.sum_mul]

private lemma equivalent_properties_sign_in_cube_helper {k : ℕ} {z : Vector k} (hz : SignVector z) : InCube z := by
  intro i
  rcases hz i with h | h
  · constructor <;> nlinarith [h]
  · constructor <;> nlinarith [h]

private lemma propertyB_to_propertyA {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (hB : PropertyB A) : PropertyA A := by
  intro x hx y hy
  exact hB x (equivalent_properties_sign_in_cube_helper hx) y
    (equivalent_properties_sign_in_cube_helper hy)

theorem equivalent_properties
    (A : Matrix (Fin m) (Fin n) ℝ) :
    PropertyA A ↔ PropertyB A ∧ PropertyC A ∧
      PropertyAAbs A ∧ PropertyBAbs A ∧ PropertyCAbs A := by
  classical
  have hnorm : 0 ≤ infNorm (fun _ : Fin n => (0 : ℝ)) :=
    infNorm_nonneg (fun _ : Fin n => (0 : ℝ))
  have sign_in_cube {k : ℕ} {z : Vector k} (hz : SignVector z) : InCube z := by
    solve_by_elim [equivalent_properties_sign_in_cube_helper]
  have sign_to_cube {k : ℕ} {z : Vector k} (hz : SignVector z) : InCube z :=
    leanflow_equivalent_properties_sign_in_cube hz
  have hsum := sum_sum_mul_right (c := fun _ : Fin m => fun _ : Fin n => (0 : ℝ))
    (t := fun _ : Fin n => (0 : ℝ))
  sorry

end MatrixSignBilinear
