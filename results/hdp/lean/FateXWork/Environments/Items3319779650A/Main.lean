import Mathlib

open scoped BigOperators

namespace FiniteIsotropicParseval

def dotProduct {n : ℕ} (u v : Fin n → ℝ) : ℝ :=
  ∑ j : Fin n, u j * v j

def Isotropic {n N : ℕ} (p : Fin N → ℝ) (x : Fin N → Fin n → ℝ) : Prop :=
  (∀ i : Fin N, 0 ≤ p i) ∧
  (∑ i : Fin N, p i : ℝ) = 1 ∧
  (∀ j k : Fin n,
    (∑ i : Fin N, p i * x i j * x i k : ℝ) =
      if j = k then (1 : ℝ) else 0)

def ParsevalFrame {n N : ℕ} (v : Fin N → Fin n → ℝ) : Prop :=
  ∀ y : Fin n → ℝ,
    (∑ i : Fin N, (dotProduct y (v i)) ^ 2 : ℝ) =
      dotProduct y y

theorem weighted_vectors_form_parseval_frame
    {n N : ℕ}
    (p : Fin N → ℝ)
    (x : Fin N → Fin n → ℝ)
    (h_isotropic : Isotropic p x) :
    ParsevalFrame (fun i : Fin N => (Real.sqrt (p i)) • x i) := by
  classical
  intro y
  unfold dotProduct
  simp only [Pi.smul_apply, smul_eq_mul]
  have hsqrt (i : Fin N) : (Real.sqrt (p i)) ^ 2 = p i :=
    Real.sq_sqrt (h_isotropic.1 i)
  calc
    ∑ i : Fin N, (∑ j : Fin n, y j * (Real.sqrt (p i) * x i j)) ^ 2 =
        ∑ i : Fin N, ∑ j : Fin n, ∑ k : Fin n,
          y j * y k * (p i * x i j * x i k) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [pow_two, Finset.sum_mul_sum]
            apply Finset.sum_congr rfl
            intro j hj
            apply Finset.sum_congr rfl
            intro k hk
            calc
              y j * (Real.sqrt (p i) * x i j) *
                  (y k * (Real.sqrt (p i) * x i k)) =
                  y j * y k * ((Real.sqrt (p i)) ^ 2 * x i j * x i k) := by ring
              _ = y j * y k * (p i * x i j * x i k) := by rw [hsqrt i]
    _ = ∑ j : Fin n, ∑ k : Fin n, y j * y k *
          (∑ i : Fin N, p i * x i j * x i k) := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro j hj
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro k hk
            rw [Finset.mul_sum]
    _ = ∑ j : Fin n, y j * y j := by
      simp [h_isotropic.2.2]
    _ = dotProduct y y := by rfl

end FiniteIsotropicParseval
