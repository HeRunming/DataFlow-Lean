import Mathlib.Probability.ProbabilityMassFunction.Binomial
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Nat.Choose.Bounds

open scoped BigOperators

private theorem exp_product_lower (k : ℕ) (a q : ℝ) (ha : 0 ≤ a) (hq : 0 ≤ q)
    (h : 1 ≤ q * (1 + a / k)) : Real.exp (-a) ≤ q ^ k := by
  have he : (1 + a / k) ^ k ≤ Real.exp a := by
    simpa [neg_div, sub_neg_eq_add] using (Real.one_sub_div_pow_le_exp_neg (n := k) (t := -a) (le_trans (neg_nonpos.mpr ha) (Nat.cast_nonneg k)))
  have hp : 1 ≤ q ^ k * (1 + a / k) ^ k := by
    simpa [mul_pow] using (one_le_pow₀ h (n := k))
  have hh : 1 ≤ q ^ k * Real.exp a := hp.trans (mul_le_mul_of_nonneg_left he (pow_nonneg hq k))
  calc
    Real.exp (-a) = 1 / Real.exp a := by rw [Real.exp_neg, one_div]
    _ ≤ q ^ k := (div_le_iff₀ (Real.exp_pos a)).2 hh

private theorem binomial_exp_lower (N t : ℕ) (a : ℝ) (hN : 0 < N) (ha : 0 ≤ a) (hat : a ≤ t) (htN : t ≤ N) :
    Real.exp (-a) ≤ (1 - a / N) ^ (N - t) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have htR : (t : ℝ) ≤ N := by exact_mod_cast htN
  by_cases he : t = N
  · subst t
    simpa using Real.exp_le_exp.mpr (neg_nonpos.mpr ha)
  have hlt : t < N := lt_of_le_of_ne htN he
  have hkN : 0 < N - t := Nat.sub_pos_of_lt hlt
  have hk : (0 : ℝ) < (N - t : ℕ) := by exact_mod_cast hkN
  have hc : ((N - t : ℕ) : ℝ) = (N : ℝ) - t := Nat.cast_sub htN
  have hprod : 1 ≤ (1-a/N)*(1+a/(N-t:ℕ)) := by
    have hi : (1-a/N)*(1+a/(N-t:ℕ))-1 = a*((t:ℝ)-a)/((N:ℝ)*(N-t:ℕ)) := by
      field_simp
      rw [hc]
      ring
    rw [← sub_nonneg]
    rw [hi]
    apply div_nonneg
    · exact mul_nonneg ha (sub_nonneg.mpr hat)
    · exact mul_nonneg hn.le hk.le
  exact exp_product_lower (N-t) a (1-a/N) ha (sub_nonneg.mpr ((div_le_one hn).mpr (hat.trans htR))) hprod

private theorem comb_choose_lower (k n : ℕ) (r : ℝ) (hr : 1 ≤ r) (hb : r*k ≤ n) : r^k ≤ (n.choose k:ℝ) := by
  induction k generalizing n with
  | zero => simp
  | succ k ih =>
    cases n with
    | zero =>
      push_cast at hb
      have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      nlinarith
    | succ n =>
      push_cast at hb
      have hb' : r*k ≤ (n:ℝ) := by nlinarith
      have hi := ih n hb'
      have hid : ((n:ℝ)+1)*(n.choose k:ℝ) = ((n+1).choose (k+1):ℝ)*((k:ℝ)+1) := by exact_mod_cast Nat.add_one_mul_choose_eq n k
      have hmul := mul_le_mul_of_nonneg_right hb (Nat.cast_nonneg (α := ℝ) (n.choose k))
      have hm := mul_le_mul_of_nonneg_left hi (le_trans (by norm_num : (0:ℝ) ≤ 1) hr)
      have hm' := mul_le_mul_of_nonneg_right hm (show (0:ℝ) ≤ (k:ℝ)+1 by positivity)
      rw [pow_succ]
      nlinarith [Nat.cast_nonneg (α := ℝ) k]

private theorem failure_real (p : NNReal) (hp : p ≤ 1) : (1 - (p : ENNReal)).toReal = 1 - (p : ℝ) := by
  rw [ENNReal.toReal_sub_of_le (by exact_mod_cast hp) (by simp)]
  simp

theorem reverse_chernoff_binomial
    (N : ℕ)
    (μ : ℝ)
    (hN : 0 < N)
    (hμ : 0 ≤ μ)
    (hμN : μ ≤ (N : ℝ))
    (hp : Real.toNNReal (μ / (N : ℝ)) ≤ (1 : NNReal)) :
    ∀ t : ℕ,
      μ ≤ (t : ℝ) →
      ∀ h_tN : t ≤ N,
        let i : Fin (N + 1) := ⟨t, Nat.lt_succ_of_le h_tN⟩
        ENNReal.toReal
            ((PMF.binomial (Real.toNNReal (μ / (N : ℝ))) hp N) i) ≥
          Real.exp (-μ) * (μ / (t : ℝ)) ^ t := by
  intro t hμt htN
  by_cases ht : t = 0
  · subst t
    have hz : μ = 0 := le_antisymm (by simpa using hμt) hμ
    subst μ
    simp [PMF.binomial_apply]
  have ht0 : (0 : ℝ) < t := by exact_mod_cast Nat.pos_of_ne_zero ht
  have hn0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hp0 : 0 ≤ μ / (N : ℝ) := div_nonneg hμ hn0.le
  have he := binomial_exp_lower N t μ hN hμ hμt htN
  have hc := comb_choose_lower t N ((N:ℝ)/t)
    ((le_div_iff₀ ht0).2 (by simpa using htN))
    (by rw [div_mul_cancel₀ _ (ne_of_gt ht0)])
  have hh := mul_le_mul hc he (Real.exp_pos _).le (Nat.cast_nonneg (N.choose t))
  have hh' := mul_le_mul_of_nonneg_left hh (pow_nonneg hp0 t)
  have hid : (μ/(N:ℝ))^t * ((N:ℝ)/t)^t = (μ/(t:ℝ))^t := by
    rw [← mul_pow]
    congr 1
    field_simp
  have hcore : Real.exp (-μ) * (μ/(t:ℝ))^t ≤ (μ/(N:ℝ))^t * (1-μ/(N:ℝ))^(N-t) * (N.choose t:ℝ) := by
    calc
      _ = ((μ/(N:ℝ))^t * ((N:ℝ)/t)^t) * Real.exp (-μ) := by rw [hid]; ring
      _ ≤ (μ/(N:ℝ))^t * ((N.choose t:ℝ) * (1-μ/(N:ℝ))^(N-t)) := by simpa only [mul_assoc] using hh'
      _ = _ := by ring
  simpa [PMF.binomial_apply, failure_real _ hp, Real.coe_toNNReal, max_eq_left hp0] using hcore
