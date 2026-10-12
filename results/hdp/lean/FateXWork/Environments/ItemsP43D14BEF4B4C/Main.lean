import Mathlib.Combinatorics.SimpleGraph.Finite

theorem degree_is_number_of_incident_edges {V : Type*} (G : SimpleGraph V) (v : V)
    [Fintype (G.neighborSet v)] [DecidableEq V] :
    (G.incidenceFinset v).card = G.degree v := by
  sorry
