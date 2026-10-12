import Mathlib

namespace HDPItem.ItemsP9F12AA861C8

namespace ApproximateCaratheodory

private def simplexVertex (n : ℕ) (i : Fin (n + 1)) : Fin (n + 1) → ℝ :=
  fun j => if j = i then (1 : ℝ) else 0

theorem simplex_exact_bound_is_tight (n : ℕ) :
    (fun _ : Fin (n + 1) => (1 : ℝ) / ((n + 1 : ℕ) : ℝ)) ∈
        convexHull ℝ (Set.range (simplexVertex n)) ∧
      ∀ t : Finset (Fin (n + 1)),
        (fun _ : Fin (n + 1) => (1 : ℝ) / ((n + 1 : ℕ) : ℝ)) ∈
          convexHull ℝ (simplexVertex n '' (t : Set (Fin (n + 1)))) →
        n + 1 ≤ t.card := by
  sorry

theorem approximate_convex_hull_dimension_independent_with_radius
    (ε : ℝ) (hε : 0 < ε) :
    ∃ k : ℕ,
      ∀ (n : ℕ) (R : ℝ) (S : Set (EuclideanSpace ℝ (Fin n)))
        (x : EuclideanSpace ℝ (Fin n)),
        0 ≤ R →
        (∀ z : EuclideanSpace ℝ (Fin n), z ∈ S → ‖z‖ ≤ R) →
        x ∈ convexHull ℝ S →
        ∃ t : Finset (EuclideanSpace ℝ (Fin n)),
          (t : Set (EuclideanSpace ℝ (Fin n))) ⊆ S ∧
          t.card ≤ k ∧
          ∃ y : EuclideanSpace ℝ (Fin n),
            y ∈ convexHull ℝ (t : Set (EuclideanSpace ℝ (Fin n))) ∧
            ‖x - y‖ < ε * (R + 1) := by
  sorry

end ApproximateCaratheodory

end HDPItem.ItemsP9F12AA861C8
