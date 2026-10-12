import Mathlib.Topology.MetricSpace.CoveringNumbers

universe u

 theorem externalCoveringNumber_le_coveringNumber_le_externalCoveringNumber_half
    {X : Type u} [PseudoMetricSpace X] (K : Set X) (ε : NNReal) :
    Metric.externalCoveringNumber ε K ≤ Metric.coveringNumber ε K ∧
      Metric.coveringNumber ε K ≤
        Metric.externalCoveringNumber (ε / (2 : NNReal)) K := by
  refine ⟨Metric.externalCoveringNumber_le_coveringNumber ε K, ?_⟩
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
    (Metric.coveringNumber_two_mul_le_externalCoveringNumber (ε / 2) K)
