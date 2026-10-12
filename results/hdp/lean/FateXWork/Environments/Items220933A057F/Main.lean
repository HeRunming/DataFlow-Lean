import Mathlib

noncomputable section

open scoped BigOperators
open MeasureTheory ProbabilityTheory

abbrev RGEdge (n : ℕ) := {e : Fin n × Fin n // e.1 < e.2}

abbrev RGGraph (n : ℕ) := Set (RGEdge n)

def edgeLeft {n : ℕ} (e : RGEdge n) : Fin n := e.1.1

def edgeRight {n : ℕ} (e : RGEdge n) : Fin n := e.1.2

noncomputable def crossingEdgeCount {n : ℕ} (G : RGGraph n)
    (S T : Finset (Fin n)) : ℕ := by
  classical
  exact
    ((Finset.univ : Finset (RGEdge n)).filter (fun e : RGEdge n =>
      e ∈ G ∧
        ((edgeLeft e ∈ S ∧ edgeRight e ∈ T) ∨
          (edgeLeft e ∈ T ∧ edgeRight e ∈ S)))).card

def GoodGraph (n : ℕ) (C p : ℝ) (G : RGGraph n) : Prop :=
  ∀ S T : Finset (Fin n),
    Disjoint S T →
    C * (n : ℝ) / p ≤ (S.card : ℝ) * (T.card : ℝ) →
    ((9 : ℝ) / (10 : ℝ)) * p ≤
        (crossingEdgeCount G S T : ℝ) /
          ((S.card : ℝ) * (T.card : ℝ)) ∧
      (crossingEdgeCount G S T : ℝ) /
          ((S.card : ℝ) * (T.card : ℝ)) ≤ ((11 : ℝ) / (10 : ℝ)) * p

def randomGraphEvent (n : ℕ) (C p : ℝ) : Set (RGGraph n) :=
  {G | GoodGraph n C p G}

def realToUnitInterval (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ (1 : ℝ)) : unitInterval :=
  ⟨p, hp0, hp1⟩

theorem random_graph_edge_density :
    ∃ C : ℝ, 0 < C ∧
      ∀ n : ℕ, 0 < n →
        ∀ p : ℝ, (hp : 0 < p) → (hp1 : p ≤ (1 : ℝ)) →
          let pI : unitInterval := realToUnitInterval p (le_of_lt hp) hp1
          let event : Set (RGGraph n) := randomGraphEvent n C p
          ∃ m : MeasurableSpace (RGGraph n),
            @MeasurableSet (RGGraph n) m event ∧
              ((ProbabilityTheory.setBernoulli
                (ι := RGEdge n) (Set.univ : Set (RGEdge n)) pI) event).toReal ≥
                (1 : ℝ) - (2 : ℝ) ^ n := by
  sorry
