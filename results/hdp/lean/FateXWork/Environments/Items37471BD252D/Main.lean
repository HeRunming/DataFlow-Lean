import Mathlib

def sourceInnerProduct {α : Type*} [Fintype α] (x y : α → ℝ) : ℝ :=
  ((∑ a : α, (x a * y a : ℝ)) : ℝ)

def sourceTensorPower {n : ℕ} (u : Fin n → ℝ) (k : ℕ) : (Fin k → Fin n) → ℝ :=
  fun coeff => ((∏ j : Fin k, (u (coeff j) : ℝ)) : ℝ)

set_option maxHeartbeats 2000000 in
theorem tensor_power_inner_product (n k : ℕ) (u v : Fin n → ℝ) :
    sourceInnerProduct (sourceTensorPower u k) (sourceTensorPower v k) =
      ((sourceInnerProduct u v : ℝ) ^ k) := by
  classical
  induction k with
  | zero => simp [sourceInnerProduct, sourceTensorPower]
  | succ k ih =>
    let e : (Fin (k + 1) → Fin n) ≃ (Fin n × (Fin k → Fin n)) :=
      { toFun := fun f => (f 0, fun (i : Fin k) => f (Fin.succ i))
        invFun := fun p => Fin.cases p.1 (fun (i : Fin k) => p.2 i)
        left_inv := by
          intro f
          funext i
          refine Fin.cases ?_ (fun j => ?_) i <;> rfl
        right_inv := by
          intro p
          rcases p with ⟨a, f⟩
          rfl }
    simp only [sourceInnerProduct, sourceTensorPower, Fin.prod_univ_succ]
    calc
      (∑ x : Fin (k + 1) → Fin n, (u (x 0) * ∏ (i : Fin k), u (x (Fin.succ i))) *
        (v (x 0) * ∏ (i : Fin k), v (x (Fin.succ i)))) =
          ∑ p : Fin n × (Fin k → Fin n),
            (u p.1 * ∏ (i : Fin k), u (p.2 i)) * (v p.1 * ∏ (i : Fin k), v (p.2 i)) := by
        apply Fintype.sum_equiv e
        intro x
        rfl
      _ = (∑ a : Fin n, u a * v a) * (∑ x : Fin k → Fin n, (∏ (i : Fin k), u (x i)) * ∏ (i : Fin k), v (x i)) := by
        rw [Fintype.sum_prod_type]
        simp_rw [mul_mul_mul_comm]
        calc
          (∑ a : Fin n, ∑ x : Fin k → Fin n, (u a * v a) * ((∏ i, u (x i)) * ∏ i, v (x i))) =
              ∑ a : Fin n, (u a * v a) * ∑ x : Fin k → Fin n, (∏ i, u (x i)) * ∏ i, v (x i) := by
            congr 1
            funext a
            rw [Finset.mul_sum]
          _ = (∑ a : Fin n, u a * v a) * (∑ x : Fin k → Fin n, (∏ i, u (x i)) * ∏ i, v (x i)) := by
            rw [Finset.sum_mul]
      _ = (∑ a : Fin n, u a * v a) ^ (k + 1) := by
        have h : (∑ x : Fin k → Fin n, (∏ (i : Fin k), u (x i)) * ∏ (i : Fin k), v (x i)) =
            (∑ a : Fin n, u a * v a) ^ k := by
          simpa [sourceInnerProduct, sourceTensorPower] using ih
        rw [h]
        ring
