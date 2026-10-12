import Mathlib

open scoped BigOperators
open MeasureTheory

noncomputable section

namespace UniformLpNorms

def ellPNorm {n : ℕ} (x : Fin n → ℝ) (p : ℝ) : ℝ :=
  Real.rpow (∑ i : Fin n, Real.rpow |x i| p) (1 / p)

def uniformMeasure (n : ℕ) : Measure (Fin n) :=
  ProbabilityTheory.uniformOn Set.univ

def lpNorm {n : ℕ} (X : Fin n → ℝ) (p : ℝ) : ℝ :=
  Real.rpow
    ((1 / (n : ℝ)) * (∑ i : Fin n, Real.rpow |X i| p))
    (1 / p)

theorem uniform_lp_norm_relation
    {n : ℕ} (hn : 0 < n) {p : ℝ} (hp : 0 < p)
    (X : Fin n → ℝ)
    (hX_measurable : Measurable X)
    (hX_integrable : Integrable X (uniformMeasure n)) :
    lpNorm X p = Real.rpow (n : ℝ) (-1 / p) * ellPNorm X p := by
  have := hp
  have := hX_measurable
  have := hX_integrable
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hn0 : 0 ≤ (n : ℝ) := le_of_lt hn'
  have hninv : 0 ≤ (n : ℝ)⁻¹ := le_of_lt (inv_pos.mpr hn')
  let S : ℝ := ∑ i : Fin n, Real.rpow |X i| p
  have hS : 0 ≤ S := by
    dsimp [S]
    exact Finset.sum_nonneg fun i hi => Real.rpow_nonneg (abs_nonneg _) _
  simp only [lpNorm, ellPNorm, one_div]
  change ((n : ℝ)⁻¹ * S) ^ (p⁻¹) = (n : ℝ) ^ (-1 / p) * S ^ (p⁻¹)
  calc
    ((n : ℝ)⁻¹ * S) ^ (p⁻¹) = ((n : ℝ)⁻¹) ^ (p⁻¹) * S ^ (p⁻¹) := by
      exact Real.mul_rpow hninv hS
    _ = ((n : ℝ) ^ (p⁻¹))⁻¹ * S ^ (p⁻¹) := by
      rw [Real.inv_rpow hn0]
    _ = (n : ℝ) ^ (-(p⁻¹)) * S ^ (p⁻¹) := by
      rw [← Real.rpow_neg hn0]
    _ = (n : ℝ) ^ (-1 / p) * S ^ (p⁻¹) := by
      rw [show -(p⁻¹) = -1 / p by ring]

end UniformLpNorms
