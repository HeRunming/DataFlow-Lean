import Mathlib

open scoped BigOperators

noncomputable def headCount (N : ℕ) (ω : Fin N → Bool) : ℕ :=
  (Finset.univ.filter (fun i : Fin N => ω i = true)).card

noncomputable def fairMass (N : ℕ) (k : ℕ) : ℝ :=
  (Nat.choose N k : ℝ) / (2 : ℝ) ^ N

noncomputable def headMass (N : ℕ) (k : ℕ) : ℝ :=
  (∑ ω : Fin N → Bool, if headCount N ω = k then (1 : ℝ) / (2 : ℝ) ^ N else (0 : ℝ))

noncomputable def uniformExpectation (N : ℕ) (f : (Fin N → Bool) → ℝ) : ℝ :=
  (∑ ω : Fin N → Bool, f ω * ((1 : ℝ) / (2 : ℝ) ^ N))

noncomputable def uniformVariance (N : ℕ) (f : (Fin N → Bool) → ℝ) : ℝ :=
  (∑ ω : Fin N → Bool, (f ω - uniformExpectation N f) ^ 2 * ((1 : ℝ) / (2 : ℝ) ^ N))

noncomputable def binomExpectation (N : ℕ) : ℝ :=
  (N : ℝ) / (2 : ℝ)

noncomputable def binomVariance (N : ℕ) : ℝ :=
  (N : ℝ) / (4 : ℝ)

private theorem headCount_cons (N : ℕ) (b : Bool) (ω : Fin N → Bool) :
    headCount (N + 1) (Fin.cons b ω) = headCount N ω + if b then 1 else 0 := by
  classical
  have hs (M : ℕ) (v : Fin M → Bool) : headCount M v = ∑ i : Fin M, if v i then 1 else 0 := by simp [headCount]
  rw [hs, Fin.sum_univ_succ, hs]
  simp [Nat.add_comm]

private theorem sum_fin_bool (N : ℕ) (f : (Fin (N + 1) → Bool) → ℝ) :
    ∑ ω : Fin (N + 1) → Bool, f ω =
      ∑ p : Bool × (Fin N → Bool), f (Fin.cons p.1 p.2) := by
  classical
  let e : (Bool × (Fin N → Bool)) ≃ (Fin (N + 1) → Bool) :=
    { toFun := fun p => Fin.cons p.1 p.2
      invFun := fun ω => (ω 0, fun i => ω i.succ)
      left_inv := by
        intro p
        rcases p with ⟨b, v⟩
        simp [Fin.cons]
      right_inv := by
        intro ω
        funext i
        refine Fin.cases ?_ (fun j => ?_) i
        · simp [Fin.cons]
        · simp [Fin.cons] }
  exact (Equiv.sum_comp e f).symm

private lemma sum_bool {α : Type*} [Fintype α] (g : Bool → α → ℝ) :
    (∑ b : Bool, ∑ x : α, g b x) =
      (∑ x : α, g false x) + ∑ x : α, g true x := by
  classical
  rw [show (Finset.univ : Finset Bool) = {false, true} by decide]
  simp

private lemma headMass_succ_zero (n : ℕ) :
    headMass (n + 1) 0 = headMass n 0 / 2 := by
  classical
  unfold headMass
  rw [sum_fin_bool, Fintype.sum_prod_type, sum_bool]
  simp [headCount_cons, pow_succ]
  calc
    (∑ x, if headCount n x = 0 then (2 : ℝ)⁻¹ * ((2 : ℝ) ^ n)⁻¹ else 0) =
        ∑ x, (if headCount n x = 0 then ((2 : ℝ) ^ n)⁻¹ else 0) / 2 := by
          apply Finset.sum_congr rfl
          intro x hx
          split <;> ring
    _ = (∑ x, if headCount n x = 0 then ((2 : ℝ) ^ n)⁻¹ else 0) / 2 := by
          rw [Finset.sum_div]

private lemma headMass_succ_succ (n k : ℕ) :
    headMass (n + 1) (k + 1) = (headMass n k + headMass n (k + 1)) / 2 := by
  classical
  unfold headMass
  rw [sum_fin_bool, Fintype.sum_prod_type, sum_bool]
  simp [headCount_cons, pow_succ]
  have h (p : Prop) [Decidable p] (a : ℝ) :
      (if p then 2⁻¹ * a else 0) = (if p then a else 0) / 2 := by
    split_ifs <;> ring
  simp_rw [h, ← Finset.sum_div]
  ring

private lemma moment_step (n : ℕ) :
    uniformExpectation (n+1) (fun ω => (headCount (n+1) ω : ℝ)) =
      uniformExpectation n (fun ω => (headCount n ω : ℝ)) + 1/2 ∧
    uniformVariance (n+1) (fun ω => (headCount (n+1) ω : ℝ)) =
      uniformVariance n (fun ω => (headCount n ω : ℝ)) + 1/4 := by
  classical
  have hn : (∑ ω : Fin n → Bool, (1 : ℝ) / 2^n) = 1 := by simp
  have hq : (2 : ℝ)^(n+1) = 2^n*2 := pow_succ _ _
  have he : uniformExpectation (n+1) (fun ω => (headCount (n+1) ω : ℝ)) =
      uniformExpectation n (fun ω => (headCount n ω : ℝ)) + 1/2 := by
    unfold uniformExpectation
    rw [sum_fin_bool, Fintype.sum_prod_type, sum_bool, ← Finset.sum_add_distrib]
    simp only [headCount_cons, Bool.false_eq_true, ↓reduceIte, Nat.add_zero,
      Nat.cast_add, Nat.cast_one, hq]
    have hi (x q : ℝ) : x * (1 / (q*2)) + (x+1) * (1/(q*2)) = x*(1/q)+(1/q)/2 := by ring
    simp_rw [hi]
    rw [Finset.sum_add_distrib, ← Finset.sum_div, hn]
  refine ⟨he, ?_⟩
  unfold uniformVariance
  rw [he, sum_fin_bool, Fintype.sum_prod_type, sum_bool, ← Finset.sum_add_distrib]
  simp only [headCount_cons, Bool.false_eq_true, ↓reduceIte, Nat.add_zero,
    Nat.cast_add, Nat.cast_one, hq]
  have hi (x m q : ℝ) : (x-(m+1/2))^2*(1/(q*2)) +
      (x+1-(m+1/2))^2*(1/(q*2)) = (x-m)^2*(1/q)+(1/q)/4 := by ring
  simp_rw [hi]
  rw [Finset.sum_add_distrib, ← Finset.sum_div, hn]

theorem fair_coin_heads_binomial (N : ℕ) :
    (∀ k : ℕ, headMass N k = fairMass N k) ∧
    uniformExpectation N (fun ω : Fin N → Bool => (headCount N ω : ℝ)) = binomExpectation N ∧
    uniformVariance N (fun ω : Fin N → Bool => (headCount N ω : ℝ)) = binomVariance N := by
  classical
  induction N with
  | zero =>
      refine ⟨?_, ?_, ?_⟩
      · intro k
        cases k <;> simp [headMass, fairMass, headCount]
      · simp [uniformExpectation, binomExpectation, headCount]
      · simp [uniformVariance, binomVariance, uniformExpectation, headCount]
  | succ n ih =>
      rcases ih with ⟨hm, he, hv⟩
      refine ⟨?_, ?_, ?_⟩
      · intro k
        cases k with
        | zero =>
            rw [headMass_succ_zero, hm 0]
            simp [fairMass, pow_succ]
            field_simp [pow_ne_zero]
        | succ k =>
            rw [headMass_succ_succ, hm k, hm (k + 1)]
            simp [fairMass, pow_succ, Nat.choose_succ_succ]
            field_simp [pow_ne_zero]
      · have hmom := moment_step n
        rw [hmom.1, he]
        simp [binomExpectation]
        ring
      · have hmom := moment_step n
        rw [hmom.2, hv]
        simp [binomVariance]
        ring
