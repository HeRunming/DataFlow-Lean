import Mathlib

/-- Number of heads in a sequence of Boolean coin tosses. -/
def heads {N : ℕ} (ω : Fin N → Bool) : ℕ :=
  (Finset.univ.filter (fun i : Fin N => ω i = true)).card

private theorem heads_fiber_card (N k : ℕ) :
    Fintype.card {ω : Fin N → Bool // heads ω = k} = N.choose k := by
  classical
  let e : {ω : Fin N → Bool // heads ω = k} ≃ {s : Finset (Fin N) // s.card = k} :=
    { toFun := fun ω => ⟨Finset.univ.filter (fun i => ω.val i = true), ω.property⟩
      invFun := fun s => ⟨fun i => decide (i ∈ s.val), by simpa [heads] using s.property⟩
      left_inv := by
        intro ω
        apply Subtype.ext
        funext i
        simp
      right_inv := by
        intro s
        apply Subtype.ext
        ext i
        simp }
  simpa using (Fintype.card_congr e).trans (Fintype.card_finset_len k)

private theorem heads_le_length (N : ℕ) (ω : Fin N → Bool) : heads ω ≤ N := by
  classical
  simpa [heads] using (Finset.card_le_univ (Finset.filter (fun i : Fin N => ω i = true) Finset.univ))

private theorem sum_interval_subtype (s : Finset ℕ) (f : ℕ → ℝ) :
    (∑ x : {k // k ∈ s}, f x.val) = ∑ k ∈ s, f k := by
  classical
  apply Finset.sum_bij (fun x _ => x.val)
  · intro x hx
    exact x.property
  · intro x hx y hy h
    exact Subtype.ext h
  · intro k hk
    exact ⟨⟨k, hk⟩, Finset.mem_univ _, rfl⟩
  · intro x hx
    rfl

theorem three_fourths_threshold_four_step (N : ℕ) :
    (3 * (N + 4) + 3) / 4 = (3 * N + 3) / 4 + 3 := by
  omega

theorem probability_at_least_three_fourths_heads (N : ℕ) :
    ((Fintype.card {ω : Fin N → Bool // 4 * heads ω ≥ 3 * N} : ℝ) / ((2 : ℝ) ^ N)) =
      (Finset.sum (Finset.Icc ((3 * N + 3) / 4) N)
        (fun k : ℕ => ((Nat.choose N k : ℕ) : ℝ) / ((2 : ℝ) ^ N))) := by
  classical
  have hfiber (k : ℕ) :
      Fintype.card {ω : Fin N → Bool // heads ω = k} = N.choose k :=
    heads_fiber_card N k
  have hsum :
      (∑ x : {k // k ∈ Finset.Icc ((3 * N + 3) / 4) N},
        (N.choose x.val : ℝ)) =
        ∑ k ∈ Finset.Icc ((3 * N + 3) / 4) N, (N.choose k : ℝ) := by
    exact sum_interval_subtype (Finset.Icc ((3 * N + 3) / 4) N)
      (fun k => (N.choose k : ℝ))
  let e : {ω : Fin N → Bool // 4 * heads ω ≥ 3 * N} ≃
      Σ k : {k : ℕ // k ∈ Finset.Icc ((3 * N + 3) / 4) N},
        {ω : Fin N → Bool // heads ω = k} :=
    { toFun := fun ω =>
        ⟨⟨heads ω.val, by
          have hle := heads_le_length N ω.val
          have hp := ω.property
          simp only [Finset.mem_Icc]
          omega⟩, ⟨ω.val, rfl⟩⟩
      invFun := fun x =>
        ⟨x.2.val, by
          have hk := x.1.property
          have heq := x.2.property
          simp only [Finset.mem_Icc] at hk
          omega⟩
      left_inv := by
        intro ω
        rfl
      right_inv := by
        rintro ⟨⟨k, hk⟩, ⟨ω, heq⟩⟩
        dsimp at heq
        subst k
        rfl }
  rw [Fintype.card_congr e, Fintype.card_sigma]
  simp only [Nat.cast_sum]
  rw [← Finset.sum_div]
  congr 1
  simp only [heads_fiber_card]
  exact hsum
