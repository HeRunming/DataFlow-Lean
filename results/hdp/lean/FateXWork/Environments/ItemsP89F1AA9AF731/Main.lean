import Mathlib

/--
Source: `HDP/source/environments.json:301-301`, fact `p89.f1`.

Source proof: The source is a one-sentence assertion and supplies no proof text.
Proof sketch: A concrete formalization should encode maximum cut and establish
NP-hardness by a polynomial reduction from a standard NP-hard problem.
Prover notes: The graph representation, decision/optimization encoding, and
complexity model are deliberately abstract here because they are not specified
by the source. The opaque interfaces must be refined if full complexity-theory
coverage is required.
-/
opaque MaximumCutProblem : Type

/-- Abstract NP-hardness predicate used to record the source claim. -/
opaque NP_Hard : Type → Prop

/-- Finding the maximum cut is generally computationally hard (NP-hard). -/
theorem maximum_cut_is_NP_hard : NP_Hard MaximumCutProblem := by
  sorry
