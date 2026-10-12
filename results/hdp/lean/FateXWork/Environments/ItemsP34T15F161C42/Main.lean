import Mathlib

open MeasureTheory Filter

noncomputable section

namespace DeMoivreLaplace

/-- Normalized head count for N independent fair coin tosses. -/
def normalizedHeads (N k : ℕ) : ℝ :=
  ((k : ℝ) - (N : ℝ) / (2 : ℝ)) /
    Real.sqrt ((N : ℝ) / (4 : ℝ))

/-- CDF of the normalized binomial head count. -/
def normalizedHeadsCDF (N : ℕ) (x : ℝ) : ℝ :=
  Finset.sum (Finset.range (N + 1) : Finset ℕ)
    (fun (k : ℕ) =>
      if normalizedHeads N k ≤ x then
        (Nat.choose N k : ℝ) / (2 : ℝ) ^ N
      else
        (0 : ℝ))

/-- CDF of the standard normal distribution. -/
def standardNormalCDF (x : ℝ) : ℝ :=
  (1 : ℝ) / Real.sqrt ((2 : ℝ) * Real.pi) *
    (∫ t in Set.Iic x,
      Real.exp (-((t : ℝ) ^ (2 : ℕ)) / (2 : ℝ)))

private lemma normalizedHeads_le_iff (N k : ℕ) (hN : 0 < N) (x : ℝ) :
    normalizedHeads N k ≤ x ↔
      (k : ℝ) ≤ (N : ℝ) / 2 + x * Real.sqrt ((N : ℝ) / 4) := by
  have h : 0 < Real.sqrt ((N : ℝ) / 4) := Real.sqrt_pos.2 (by positivity)
  rw [normalizedHeads, div_le_iff₀ h]
  constructor <;> intro hk <;> linarith

private lemma normalizedHeadsCDF_eq_sum (N : ℕ) (x : ℝ) :
    normalizedHeadsCDF N x =
      Finset.sum (Finset.range (N + 1))
        (fun k =>
          if normalizedHeads N k ≤ x then
            (Nat.choose N k : ℝ) / (2 : ℝ) ^ N
          else 0) := by
  rfl

private lemma helper_normalizedHeadsCDF_eq_sum (N : ℕ) (x : ℝ) :
    normalizedHeadsCDF N x =
      ∑ k ∈ Finset.range (N + 1),
        if normalizedHeads N k ≤ x then (N.choose k : ℝ) / 2 ^ N else 0 := by
  rfl

private lemma helper_normalizedHeads_zero (k : ℕ) : normalizedHeads 0 k = 0 := by
  simp [normalizedHeads]

private lemma tendsto_const_real (c : ℝ) :
    Filter.Tendsto (fun _ : ℕ => c) Filter.atTop (nhds c) := by
  exact tendsto_const_nhds

private lemma normalizedHeadsCDF_filter_sum (N : ℕ) (x : ℝ) :
    normalizedHeadsCDF N x =
      ∑ k ∈ (Finset.range (N + 1)).filter
        (fun k => normalizedHeads N k ≤ x),
        (Nat.choose N k : ℝ) / (2 : ℝ) ^ N := by
  simp [normalizedHeadsCDF, Finset.sum_filter]

private lemma normalizedHeads_eventually_pos : ∀ᶠ N : ℕ in Filter.atTop, 0 < N := by
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  exact hN

private lemma helper_real_tendsto_const (c : ℝ) :
    Filter.Tendsto (fun _ : ℕ => c) Filter.atTop (nhds c) := by
  exact tendsto_const_nhds

/-- De Moivre–Laplace convergence, expressed through CDFs. -/
theorem deMoivreLaplace (x : ℝ) :
    Filter.Tendsto
      (fun (N : ℕ) => normalizedHeadsCDF N x)
      Filter.atTop
      (nhds (standardNormalCDF x)) := by sorry

end DeMoivreLaplace
