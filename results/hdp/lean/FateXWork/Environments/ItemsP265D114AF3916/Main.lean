import Mathlib

/--
Source proof: The source passage is a definitional/expository statement and
contains no separate proof text.

Proof sketch: For points on the unit sphere, the length of the shortest great-
circle arc is the central angle between the points. In Euclidean coordinates,
that angle is `Real.arccos` of their real inner product.

Prover notes: The source does not specify dimension, radius, or a coordinate
representation. This declaration makes dimension explicit, uses the unit
sphere in `EuclideanSpace ℝ (Fin n)`, and represents the smallest-arc length by
the equivalent central-angle formula.
-/
noncomputable def geodesicDistance {n : ℕ}
    (x y : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) : ℝ :=
  Real.arccos (∑ i, (x : EuclideanSpace ℝ (Fin n)) i * (y : EuclideanSpace ℝ (Fin n)) i)
