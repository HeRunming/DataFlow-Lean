import Mathlib

private lemma choose_step {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (u v : E) :
    ‖u + v‖ ^ 2 ≤ ‖u‖ ^ 2 + ‖v‖ ^ 2 ∨
    ‖u - v‖ ^ 2 ≤ ‖u‖ ^ 2 + ‖v‖ ^ 2 := by
  have h₁ := norm_add_sq_real u v
  have h₂ := norm_sub_sq_real u v
  rcases le_total (inner ℝ u v) 0 with h | h
  · left; nlinarith
  · right; nlinarith

private lemma sign_sum_sq_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ) (v : Fin m → E) (hv : ∀ i, ‖v i‖ ≤ (1 : ℝ)) :
    ∃ σ : Fin m → ℝ,
      (∀ i, σ i = (-1 : ℝ) ∨ σ i = (1 : ℝ)) ∧
        ‖∑ i, σ i • v i‖ ^ 2 ≤ (m : ℝ) := by
  induction m with
  | zero =>
      refine ⟨fun i => Fin.elim0 i, ?_, ?_⟩
      · intro i; exact Fin.elim0 i
      · simp
  | succ m ih =>
      let vtail : Fin m → E := fun i => v i.succ
      have htail : ∀ i, ‖vtail i‖ ≤ (1 : ℝ) := by
        intro i; exact hv i.succ
      obtain ⟨τ, hτ, hτnorm⟩ := ih vtail htail
      let s : E := ∑ i : Fin m, τ i • vtail i
      have hcast : (m.succ : ℝ) = (m : ℝ) + 1 := by norm_num
      rcases choose_step s (v 0) with hplus | hminus
      · let σ : Fin (Nat.succ m) → ℝ := Fin.cases 1 τ
        refine ⟨σ, ?_, ?_⟩
        · intro i; refine Fin.cases (Or.inr rfl) (fun j => hτ j) i
        · calc
            ‖∑ i : Fin (Nat.succ m), σ i • v i‖ ^ 2 = ‖s + v 0‖ ^ 2 := by simp [Fin.sum_univ_succ, σ, s, vtail, add_comm]
            _ ≤ ‖s‖ ^ 2 + ‖v 0‖ ^ 2 := hplus
            _ ≤ (Nat.succ m : ℝ) := by
              have h0 := hv (0 : Fin (Nat.succ m))
              have hs : ‖s‖ ^ 2 ≤ (m : ℝ) := by simpa [s, vtail] using hτnorm
              have hn := norm_nonneg (v 0)
              nlinarith [hcast]
      · let σ : Fin (Nat.succ m) → ℝ := Fin.cases (-1) τ
        refine ⟨σ, ?_, ?_⟩
        · intro i; refine Fin.cases (Or.inl rfl) (fun j => hτ j) i
        · calc
            ‖∑ i : Fin (Nat.succ m), σ i • v i‖ ^ 2 = ‖s - v 0‖ ^ 2 := by
              simp [Fin.sum_univ_succ, σ, s, vtail, sub_eq_add_neg, add_comm, norm_neg]
            _ ≤ ‖s‖ ^ 2 + ‖v 0‖ ^ 2 := hminus
            _ ≤ (Nat.succ m : ℝ) := by
              have h0 := hv (0 : Fin (Nat.succ m))
              have hs : ‖s‖ ^ 2 ≤ (m : ℝ) := by simpa [s, vtail] using hτnorm
              have hn := norm_nonneg (v 0)
              nlinarith [hcast]

theorem balancing_vectors_exists_signs
    (n : ℕ)
    (x : Fin n → EuclideanSpace ℝ (Fin n))
    (h_unit : ∀ i : Fin n, ‖x i‖ ≤ (1 : ℝ)) :
    ∃ σ : Fin n → ℝ,
      (∀ i : Fin n, σ i = (-1 : ℝ) ∨ σ i = (1 : ℝ)) ∧
        ‖((Finset.univ : Finset (Fin n)).sum
          (fun i : Fin n => σ i • x i) : EuclideanSpace ℝ (Fin n))‖ ≤
          Real.sqrt (n : ℝ) := by
  classical
  obtain ⟨σ, hσ, hsq⟩ := sign_sum_sq_le n x h_unit
  refine ⟨σ, hσ, ?_⟩
  have hsqrt : (0 : ℝ) ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  have hnorm : (0 : ℝ) ≤
      ‖((Finset.univ : Finset (Fin n)).sum
        (fun i : Fin n => σ i • x i) : EuclideanSpace ℝ (Fin n))‖ := norm_nonneg _
  have hsq' :
      ‖((Finset.univ : Finset (Fin n)).sum
        (fun i : Fin n => σ i • x i) : EuclideanSpace ℝ (Fin n))‖ ^ 2 ≤ (n : ℝ) := by
    simpa using hsq
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (n : ℝ) by positivity)]

theorem balancing_vectors_radius_sharp
    (n : ℕ) :
    ∀ r : ℝ, r < Real.sqrt (n : ℝ) →
      ∃ x : Fin n → EuclideanSpace ℝ (Fin n),
        (∀ i : Fin n, ‖x i‖ ≤ (1 : ℝ)) ∧
          ∀ σ : Fin n → ℝ,
            (∀ i : Fin n, σ i = (-1 : ℝ) ∨ σ i = (1 : ℝ)) →
              r <
                ‖((Finset.univ : Finset (Fin n)).sum
                  (fun i : Fin n => σ i • x i) : EuclideanSpace ℝ (Fin n))‖ := by
  intro r hr
  let x : Fin n → EuclideanSpace ℝ (Fin n) := fun i => EuclideanSpace.single i (1 : ℝ)
  refine ⟨x, ?_, ?_⟩
  · intro i
    simp [x]
  · intro σ hσ
    have hsquares :
        ∑ i : Fin n, σ i ^ 2 = (n : ℝ) := by
      calc
        ∑ i : Fin n, σ i ^ 2 = ∑ _i : Fin n, (1 : ℝ) := by
          apply Finset.sum_congr rfl
          intro i hi
          rcases hσ i with h | h <;> simp [h]
        _ = (n : ℝ) := by simp
    rw [EuclideanSpace.norm_eq]
    simp [x, Pi.single_apply, Real.norm_eq_abs, sq_abs]
    rw [hsquares]
    exact hr
