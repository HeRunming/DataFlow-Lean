import Mathlib

open MeasureTheory

universe u

private lemma sign_support {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Ω → ℝ) (hY : Measurable Y) (hn : μ {ω | Y ω = -1} = (1 : ENNReal) / 2) (hp : μ {ω | Y ω = 1} = (1 : ENNReal) / 2) : ∀ᵐ ω ∂μ, Y ω = -1 ∨ Y ω = 1 := by
  have hd : Disjoint {ω | Y ω = (-1 : ℝ)} {ω | Y ω = (1 : ℝ)} := by
    rw [Set.disjoint_left]
    intro x hx hy
    simp only [Set.mem_setOf_eq] at hx hy
    linarith
  have hm : μ ({ω | Y ω = (-1 : ℝ)} ∪ {ω | Y ω = (1 : ℝ)}) = 1 := by
    rw [measure_union hd (hY (measurableSet_singleton 1)), hn, hp, ← ENNReal.add_div]
    norm_num only [one_add_one_eq_two]
    exact ENNReal.div_self (by norm_num) (by norm_num)
  have hs : MeasurableSet ({ω | Y ω = (-1 : ℝ)} ∪ {ω | Y ω = (1 : ℝ)}) :=
    (measurableSet_eq_fun hY measurable_const).union (measurableSet_eq_fun hY measurable_const)
  rw [ae_iff]
  change μ ({ω | Y ω = (-1 : ℝ)} ∪ {ω | Y ω = (1 : ℝ)})ᶜ = 0
  rw [measure_compl hs (measure_ne_top _ _), hm]
  simp

private lemma sign_atom {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω)
    (n : ℕ) (X : Fin n → Ω → ℝ)
    (hi : ∀ B : Fin n → Set ℝ, (∀ i, MeasurableSet (B i)) →
      μ {ω | ∀ i, X i ω ∈ B i} = ∏ i, μ {ω | X i ω ∈ B i})
    (hn : ∀ i, μ {ω | X i ω = (-1 : ℝ)} = (1 : ENNReal) / 2)
    (hp : ∀ i, μ {ω | X i ω = (1 : ℝ)} = (1 : ENNReal) / 2)
    (s : Fin n → Bool) :
    μ {ω | ∀ i, X i ω = (if s i = true then (1 : ℝ) else -1)} = ((1 : ENNReal) / 2) ^ n := by
  have h := hi (fun i => {if s i = true then (1 : ℝ) else -1}) (fun _ => measurableSet_singleton _)
  simp only [Set.mem_singleton_iff] at h
  rw [h]
  calc
    _ = ∏ _i : Fin n, ((1 : ENNReal) / 2) := by
      apply Finset.prod_congr rfl
      intro i _
      by_cases hs : s i = true
      · simpa [hs] using hp i
      · simpa [hs] using hn i
    _ = _ := by simp

private lemma two_pow_mul_half_pow (n : ℕ) :
    (2 : ENNReal) ^ n * ((1 : ENNReal) / 2) ^ n = 1 := by
  rw [← mul_pow]
  have h : (2 : ENNReal) * ((1 : ENNReal) / 2) = 1 := by
    rw [ENNReal.div_eq_inv_mul, mul_one]
    exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
  rw [h, one_pow]

theorem rademacher_weighted_sum_zero_probability_le_half
    {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n : ℕ)
    (coeff : Fin n → ℝ)
    (hcoeff : ∃ i : Fin n, coeff i ≠ (0 : ℝ))
    (X : Fin n → Ω → ℝ)
    (h_measurable : ∀ i : Fin n, Measurable (X i))
    (h_independent :
      ∀ B : Fin n → Set ℝ,
        (∀ i : Fin n, MeasurableSet (B i)) →
        μ {ω : Ω | ∀ i : Fin n, X i ω ∈ B i} =
          (Finset.univ.prod
            (fun i : Fin n => μ {ω : Ω | X i ω ∈ B i}) : ENNReal))
    (h_neg : ∀ i : Fin n,
      μ {ω : Ω | X i ω = (-1 : ℝ)} =
        (1 : ENNReal) / (2 : ENNReal))
    (h_pos : ∀ i : Fin n,
      μ {ω : Ω | X i ω = (1 : ℝ)} =
        (1 : ENNReal) / (2 : ENNReal)) :
    μ {ω : Ω |
      (Finset.univ.sum
        (fun i : Fin n => coeff i * X i ω) : ℝ) = (0 : ℝ)} ≤
      (1 : ENNReal) / (2 : ENNReal) := by
  classical
  rcases hcoeff with ⟨j, hj⟩
  let v : Bool → ℝ := fun b => if b = true then 1 else -1
  let S : Finset (Fin n → Bool) := Finset.univ.filter (fun s => ∑ i, coeff i * v (s i) = 0)
  let f : (Fin n → Bool) → (Fin n → Bool) := fun s => Function.update s j (!(s j))
  have hinv : Function.Involutive f := by
    intro s; funext i; by_cases h : i = j
    · subst i; simp [f]
    · simp [f, Function.update_of_ne h]
  have hdis : Disjoint S (S.image f) := by
    rw [Finset.disjoint_left]
    intro s hs ht
    obtain ⟨t, htS, rfl⟩ := Finset.mem_image.mp ht
    have h1 : ∑ i, coeff i * v (t i) = 0 := (Finset.mem_filter.mp htS).2
    have h2 : ∑ i, coeff i * v (f t i) = 0 := (Finset.mem_filter.mp hs).2
    have he : ∑ i ∈ Finset.univ.erase j, coeff i * v (f t i) =
        ∑ i ∈ Finset.univ.erase j, coeff i * v (t i) := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [f, Function.update_of_ne (Finset.ne_of_mem_erase hi)]
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j)] at h1 h2
    rw [he] at h2
    have hv : v (f t j) = -v (t j) := by
      cases h : t j <;> simp [f, v, h]
    rw [hv] at h2
    have hz : coeff j * v (t j) = 0 := by linarith
    have hvn : v (t j) ≠ 0 := by cases t j <;> simp [v]
    exact hj ((mul_eq_zero.mp hz).resolve_right hvn)
  have hc : 2 * S.card ≤ 2 ^ n := by
    have he : (S.image f).card = S.card := Finset.card_image_of_injective S hinv.injective
    have hu := Finset.card_le_card (Finset.subset_univ (S ∪ S.image f))
    rw [Finset.card_union_of_disjoint hdis, he] at hu
    simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at hu
    omega
  let A : (Fin n → Bool) → Set Ω := fun s => {ω | ∀ i, X i ω = v (s i)}
  have ha : ∀ s, μ (A s) = ((1 : ENNReal) / 2) ^ n := by
    intro s
    exact sign_atom μ n X h_independent h_neg h_pos s
  have hall : ∀ᵐ ω ∂μ, ∀ i, X i ω = (-1 : ℝ) ∨ X i ω = 1 :=
    (ae_all_iff).2 (fun i => sign_support μ (X i) (h_measurable i) (h_neg i) (h_pos i))
  have hsub : {ω | ∑ i, coeff i * X i ω = 0} ≤ᵐ[μ] ⋃ s ∈ S, A s := by
    filter_upwards [hall] with ω hω
    intro hz
    let s : Fin n → Bool := fun i => decide (X i ω = 1)
    have hs : ∀ i, X i ω = v (s i) := by
      intro i; rcases hω i with hn | hp
      · simp [s, v, hn]
      · simp [s, v, hp]
    have hm : s ∈ S := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      simpa only [← hs] using hz
    exact Set.mem_iUnion.mpr ⟨s, Set.mem_iUnion.mpr ⟨hm, hs⟩⟩
  have hm : μ {ω | ∑ i, coeff i * X i ω = 0} ≤ (S.card : ENNReal) * ((1 : ENNReal) / 2) ^ n := by
    calc
      _ ≤ μ (⋃ s ∈ S, A s) := measure_mono_ae hsub
      _ ≤ ∑ s ∈ S, μ (A s) := measure_biUnion_finset_le S A
      _ = _ := by simp [ha]
  have hc' : (2 : ENNReal) * S.card ≤ (2 : ENNReal) ^ n := by exact_mod_cast hc
  have hh : (2 : ENNReal) * ((S.card : ENNReal) * ((1 : ENNReal) / 2) ^ n) ≤ 1 := by
    calc
      _ = ((2 : ENNReal) * S.card) * ((1 : ENNReal) / 2) ^ n := by ring
      _ ≤ (2 : ENNReal) ^ n * ((1 : ENNReal) / 2) ^ n :=
        mul_le_mul_of_nonneg_right hc' (by positivity)
      _ = 1 := two_pow_mul_half_pow n
  exact hm.trans ((ENNReal.le_div_iff_mul_le (by norm_num) (by norm_num)).2 (by simpa [mul_comm] using hh))
