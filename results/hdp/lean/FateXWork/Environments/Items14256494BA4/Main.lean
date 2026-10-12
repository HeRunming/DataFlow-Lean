import Mathlib

noncomputable section

open MeasureTheory
open scoped BigOperators

abbrev CampusEdge (n : ℕ) := {e : Fin n × Fin n // e.1 < e.2}

instance campusEdgeFintype (n : ℕ) : Fintype (CampusEdge n) :=
  Fintype.ofFinite (CampusEdge n)

abbrev FriendshipAssignment (n : ℕ) := CampusEdge n → Bool

def Friends {n : ℕ} (ω : FriendshipAssignment n) (i j : Fin n) : Prop :=
  i ≠ j ∧
    ∃ e : CampusEdge n,
      ((e.1.1 = i ∧ e.1.2 = j) ∨ (e.1.1 = j ∧ e.1.2 = i)) ∧
        ω e = true

theorem no_friendless_students_probability
    (n : ℕ)
    (p : ℝ)
    (μ : Measure (FriendshipAssignment n))
    (hμ : IsProbabilityMeasure μ)
    (hn : 2 ≤ n)
    (hp_nonneg : 0 ≤ p)
    (hp_le_one : p ≤ 1)
    (hp : 4 * Real.log (n : ℝ) / (n : ℝ) ≤ p)
    (hmeas_coordinate :
      ∀ e : CampusEdge n,
        Measurable (fun ω : FriendshipAssignment n => ω e))
    (hmeas_friend :
      ∀ i j : Fin n,
        MeasurableSet {ω : FriendshipAssignment n | Friends ω i j})
    (hmeas_success :
      MeasurableSet {
        ω : FriendshipAssignment n |
          ∀ i : Fin n, ∃ j : Fin n, Friends ω i j
      })
    (hfriend_independent :
      ∀ f : FriendshipAssignment n,
        μ {ω : FriendshipAssignment n | ∀ e : CampusEdge n, ω e = f e} =
          (Finset.prod (Finset.univ : Finset (CampusEdge n))
            (fun e =>
              if f e = true then ENNReal.ofReal p
              else ENNReal.ofReal (1 - p)) : ENNReal)) :
    μ {
        ω : FriendshipAssignment n |
          ∀ i : Fin n, ∃ j : Fin n, Friends ω i j
      } ≥ ENNReal.ofReal (1 - (1 : ℝ) / (n : ℝ)) := by
  sorry
