import Mathlib.Topology.MetricSpace.CoveringNumbers

universe u

/-- Packing and covering inequalities at a positive radius. -/
theorem packing_covering_number_bounds
    {T : Type u} [MetricSpace T]
    (K : Set T) (ε : ℝ) (hε : (0 : ℝ) < ε) :
    let r : NNReal := ⟨ε, le_of_lt hε⟩
    Metric.packingNumber ((2 : NNReal) * r) K ≤ Metric.coveringNumber r K ∧
      Metric.coveringNumber r K ≤ Metric.packingNumber r K := by
  dsimp
  constructor
  · exact (Metric.packingNumber_two_mul_le_externalCoveringNumber _ _).trans
      (Metric.externalCoveringNumber_le_coveringNumber _ _)
  · exact Metric.coveringNumber_le_packingNumber _ _
