import Mathlib

theorem convex_set_iff (n : ℕ) (K : Set (Fin n → ℝ)) :
    Convex ℝ K ↔
      ∀ x y : Fin n → ℝ,
        x ∈ K →
        y ∈ K →
        ∀ coeff : ℝ,
          coeff ∈ Set.Icc (0 : ℝ) 1 →
            coeff • x + (1 - coeff) • y ∈ K := by
  constructor
  · intro h x y hx hy coeff hcoeff
    exact h hx hy hcoeff.1 (sub_nonneg.mpr hcoeff.2) (by ring)
  · intro h x hx y hy a b ha hb hab
    obtain rfl : b = 1 - a := by linarith
    apply h x y hx hy a
    exact ⟨ha, by linarith⟩
