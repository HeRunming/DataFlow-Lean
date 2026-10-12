import Mathlib

open scoped BigOperators

set_option autoImplicit false

namespace FiniteLp

abbrev PositiveExponent := {p : ℝ // (0 : ℝ) < p}

noncomputable def ellPNorm {n : ℕ} (p : PositiveExponent)
    (x : Fin n → ℝ) : ℝ :=
  ((∑ i : Fin n, (|x i| : ℝ) ^ (p : ℝ)) : ℝ) ^
    ((1 : ℝ) / (p : ℝ))

noncomputable def ellInfinityNorm {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  sSup ({r : ℝ | r = (0 : ℝ) ∨ ∃ i : Fin n, r = |x i|})

private lemma ell_bound_aux {n : ℕ} (x : Fin n → ℝ) :
    0 ≤ ellInfinityNorm x ∧ ∀ i, |x i| ≤ ellInfinityNorm x := by
  have hb : BddAbove {r : ℝ | r = 0 ∨ ∃ i : Fin n, r = |x i|} := by
    refine ⟨∑ i, |x i|, ?_⟩
    rintro r (rfl | ⟨i, rfl⟩)
    · exact Finset.sum_nonneg (fun i _ => abs_nonneg (x i))
    · exact Finset.single_le_sum (fun j _ => abs_nonneg (x j)) (Finset.mem_univ i)
  exact ⟨le_csSup hb (Or.inl rfl), fun i => le_csSup hb (Or.inr ⟨i, rfl⟩)⟩

theorem ellPNorm_tendsto_ellInfinityNorm
    (n : ℕ) (x : Fin n → ℝ) :
    Filter.Tendsto
      (fun p : PositiveExponent => ellPNorm p x)
      Filter.atTop
      (nhds (ellInfinityNorm x)) := by
  have bounds (p : PositiveExponent) : ellInfinityNorm x ≤ ellPNorm p x ∧
      ellPNorm p x ≤ ((n : ℝ) + 1) ^ (1 / (p : ℝ)) * ellInfinityNorm x := by
    have hp := p.property
    have hq : 0 < 1 / (p : ℝ) := one_div_pos.mpr hp
    have hs : 0 ≤ ∑ i, |x i| ^ (p : ℝ) := Finset.sum_nonneg fun i _ => Real.rpow_nonneg (abs_nonneg _) _
    have hr (a : ℝ) (ha : 0 ≤ a) : (a ^ (p : ℝ)) ^ (1 / (p : ℝ)) = a := by
      rw [← Real.rpow_mul ha, mul_one_div_cancel hp.ne', Real.rpow_one]
    constructor
    · unfold ellInfinityNorm
      apply csSup_le (show Set.Nonempty {r : ℝ | r = 0 ∨ ∃ i : Fin n, r = |x i|} from ⟨0, Or.inl rfl⟩)
      rintro r (rfl | ⟨i, rfl⟩)
      · exact Real.rpow_nonneg hs _
      · calc
          |x i| = (|x i| ^ (p : ℝ)) ^ (1 / (p : ℝ)) := (hr _ (abs_nonneg _)).symm
          _ ≤ ellPNorm p x := Real.rpow_le_rpow (Real.rpow_nonneg (abs_nonneg _) _) (Finset.single_le_sum (fun j _ => Real.rpow_nonneg (abs_nonneg _) _) (Finset.mem_univ i)) hq.le
    · have hsum : (∑ i, |x i| ^ (p : ℝ)) ≤ ((n : ℝ) + 1) * (ellInfinityNorm x) ^ (p : ℝ) := by
        calc
          _ ≤ ∑ _i : Fin n, (ellInfinityNorm x) ^ (p : ℝ) := Finset.sum_le_sum fun i _ => Real.rpow_le_rpow (abs_nonneg _) ((ell_bound_aux x).2 i) hp.le
          _ = (n : ℝ) * (ellInfinityNorm x) ^ (p : ℝ) := by simp
          _ ≤ _ := by nlinarith [Real.rpow_nonneg (ell_bound_aux x).1 (p : ℝ)]
      unfold ellPNorm
      calc
        _ ≤ (((n : ℝ) + 1) * (ellInfinityNorm x) ^ (p : ℝ)) ^ (1 / (p : ℝ)) := Real.rpow_le_rpow hs hsum hq.le
        _ = _ := by rw [Real.mul_rpow (by positivity : 0 ≤ (n : ℝ) + 1) (Real.rpow_nonneg (ell_bound_aux x).1 _), hr _ (ell_bound_aux x).1]
  have ht : Filter.Tendsto (fun p : PositiveExponent => (p : ℝ)) Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop.2
    intro b
    exact Filter.eventually_atTop.2 ⟨⟨max b 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _)⟩, fun p hp => (le_max_left b 1).trans hp⟩
  have hq : Filter.Tendsto (fun p : PositiveExponent => 1 / (p : ℝ)) Filter.atTop (nhds 0) := by
    simpa using tendsto_inv_atTop_zero.comp ht
  have hu : Filter.Tendsto (fun p : PositiveExponent => ((n : ℝ) + 1) ^ (1 / (p : ℝ)) * ellInfinityNorm x) Filter.atTop (nhds (ellInfinityNorm x)) := by
    have hh := (Filter.Tendsto.rpow tendsto_const_nhds hq (Or.inl (by positivity : (n : ℝ) + 1 ≠ 0))).mul_const (ellInfinityNorm x)
    simpa using hh
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu (fun p => (bounds p).1) (fun p => (bounds p).2)

 theorem ellPNorm_bounds_of_log_le
    (n : ℕ) (hn : 0 < n) (x : Fin n → ℝ)
    (p : PositiveExponent)
    (hp_log : Real.log (n : ℝ) ≤ (p : ℝ)) :
    ellInfinityNorm x ≤ ellPNorm p x ∧
      ellPNorm p x ≤ Real.exp (1 : ℝ) * ellInfinityNorm x := by
  have hp := p.property
  have hM := (ell_bound_aux x).1
  have hs : 0 ≤ ∑ i, |x i| ^ (p : ℝ) :=
    Finset.sum_nonneg fun i _ => Real.rpow_nonneg (abs_nonneg _) _
  have hr (a : ℝ) (ha : 0 ≤ a) : (a ^ (p : ℝ)) ^ (1 / (p : ℝ)) = a := by
    rw [← Real.rpow_mul ha, mul_one_div_cancel hp.ne', Real.rpow_one]
  constructor
  · unfold ellInfinityNorm
    apply csSup_le (show Set.Nonempty {r : ℝ | r = 0 ∨ ∃ i : Fin n, r = |x i|} from ⟨0, Or.inl rfl⟩)
    rintro r (rfl | ⟨i, rfl⟩)
    · exact Real.rpow_nonneg hs _
    · calc
        |x i| = (|x i| ^ (p : ℝ)) ^ (1 / (p : ℝ)) := (hr _ (abs_nonneg _)).symm
        _ ≤ ellPNorm p x := Real.rpow_le_rpow (Real.rpow_nonneg (abs_nonneg _) _) (Finset.single_le_sum (fun j _ => Real.rpow_nonneg (abs_nonneg _) _) (Finset.mem_univ i)) (one_div_pos.mpr hp).le
  · have hsum : (∑ i, |x i| ^ (p : ℝ)) ≤ (n : ℝ) * (ellInfinityNorm x) ^ (p : ℝ) := by
      calc
        _ ≤ ∑ _i : Fin n, (ellInfinityNorm x) ^ (p : ℝ) := Finset.sum_le_sum fun i _ => Real.rpow_le_rpow (abs_nonneg _) ((ell_bound_aux x).2 i) hp.le
        _ = _ := by simp
    have hn0 : 0 < (n : ℝ) := by exact_mod_cast hn
    have he : (n : ℝ) ^ (1 / (p : ℝ)) ≤ Real.exp 1 := by
      rw [Real.rpow_def_of_pos hn0]
      apply Real.exp_le_exp.mpr
      rw [mul_one_div]
      exact (div_le_one hp).mpr hp_log
    calc
      ellPNorm p x ≤ ((n : ℝ) * (ellInfinityNorm x) ^ (p : ℝ)) ^ (1 / (p : ℝ)) := Real.rpow_le_rpow hs hsum (one_div_pos.mpr hp).le
      _ = (n : ℝ) ^ (1 / (p : ℝ)) * ellInfinityNorm x := by
        rw [Real.mul_rpow hn0.le (Real.rpow_nonneg hM _), hr _ hM]
      _ ≤ _ := mul_le_mul_of_nonneg_right he hM

end FiniteLp
