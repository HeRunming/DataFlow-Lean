import Mathlib

namespace ErdosRenyi

universe u

/-- Unordered pairs of distinct vertices from `Fin n`. -/
def EdgeIndex (n : ℕ) := {s : Finset (Fin n) // s.card = 2}

/-- A probability model for the Erdős–Rényi random graph `G(n,p)`. -/
structure ErdosRenyiModel (n : ℕ) (p : ℝ) (Ω : Type u) [MeasurableSpace Ω] where
  probability : MeasureTheory.Measure Ω
  probability_univ : probability Set.univ = (1 : ENNReal)
  edge : EdgeIndex n → Ω → Bool
  measurable_edge : ∀ i : EdgeIndex n, Measurable (edge i)
  probability_parameter : (0 : ℝ) ≤ p ∧ p ≤ (1 : ℝ)
  edge_probability :
    ∀ i : EdgeIndex n,
      probability {ω : Ω | edge i ω = true} = ENNReal.ofReal p
  edges_mutually_independent :
    ∀ (S : Finset (EdgeIndex n)) (a : EdgeIndex n → Bool),
      probability {ω : Ω | ∀ i ∈ S, edge i ω = a i} =
        Finset.prod S (fun i => probability {ω : Ω | edge i ω = a i})

theorem erdosRenyiModel_has_independent_edges
    {n : ℕ} {p : ℝ} {Ω : Type u} [MeasurableSpace Ω]
    (M : ErdosRenyiModel n p Ω) :
    ∀ (S : Finset (EdgeIndex n)) (a : EdgeIndex n → Bool),
      M.probability {ω : Ω | ∀ i ∈ S, M.edge i ω = a i} =
        Finset.prod S (fun i => M.probability {ω : Ω | M.edge i ω = a i}) := by
  sorry

end ErdosRenyi
