import Mathlib

namespace PolytopeVolumeBound

/-- The convex hull of an explicitly indexed finite family. -/
def finiteConvexHull {n N : ℕ}
    (v : Fin N → EuclideanSpace ℝ (Fin n)) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {x | ∃ coeff : Fin N → ℝ,
    (∀ i : Fin N, (0 : ℝ) ≤ coeff i) ∧
    ((∑ i : Fin N, coeff i) : ℝ) = (1 : ℝ) ∧
    ((∑ i : Fin N, coeff i • v i) : EuclideanSpace ℝ (Fin n)) = x}

/-- A vertex is an extreme point, using strict convex combinations. -/
def IsVertex {n : ℕ} (P : Set (EuclideanSpace ℝ (Fin n)))
    (x : EuclideanSpace ℝ (Fin n)) : Prop :=
  x ∈ P ∧
    ∀ (y z : EuclideanSpace ℝ (Fin n)),
      y ∈ P → z ∈ P →
      ∀ t : ℝ, (0 : ℝ) < t → t < (1 : ℝ) →
        x = t • y + ((1 : ℝ) - t) • z → y = x ∧ z = x

/-- The closed unit Euclidean ball. -/
def unitBall (n : ℕ) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | ‖x‖ ≤ (1 : ℝ)}

private theorem finiteConvexHull_one (n : ℕ) (v : Fin 1 → EuclideanSpace ℝ (Fin n)) : finiteConvexHull v = {v 0} := by
  ext x
  constructor
  · rintro ⟨c, _, hc, hx⟩
    simp only [Fin.sum_univ_one] at hc hx
    simpa [hc] using hx.symm
  · intro hx
    have hx' : x = v 0 := hx
    subst x
    refine ⟨fun _ => 1, ?_, ?_, ?_⟩ <;> simp

private lemma finiteConvexHull_subset_unitBall
    (n N : ℕ)
    (P : Set (EuclideanSpace ℝ (Fin n)))
    (v : Fin N → EuclideanSpace ℝ (Fin n))
    (hpolytope : P = finiteConvexHull v)
    (hcontained : P ⊆ unitBall n) :
    finiteConvexHull v ⊆ unitBall n := by
  rw [← hpolytope]
  exact hcontained

private lemma contained_volume_ratio_le_one (n : ℕ)
    (P : Set (EuclideanSpace ℝ (Fin n))) (hP : P ⊆ unitBall n) :
    (MeasureTheory.volume P).toReal / (MeasureTheory.volume (unitBall n)).toReal ≤ 1 := by
  have hb : MeasureTheory.volume (unitBall n) ≠ ⊤ := by
    have he : unitBall n = Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 := by
      ext x
      simp [unitBall, Metric.mem_closedBall, dist_zero_right]
    rw [he]
    exact (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) 1).measure_ne_top
  have hm := ENNReal.toReal_mono hb (MeasureTheory.measure_mono hP)
  by_cases hz : (MeasureTheory.volume (unitBall n)).toReal = 0
  · simp [hz]
  · apply (div_le_iff₀ (lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hz))).2
    simpa using hm

/-- The volume estimate (0.2). -/
theorem volume_ratio_le
    (n N : ℕ)
    (hn : 0 < n)
    (hN : 0 < N)
    (P : Set (EuclideanSpace ℝ (Fin n)))
    (v : Fin N → EuclideanSpace ℝ (Fin n))
    (hinjective : Function.Injective v)
    (hpolytope : P = finiteConvexHull v)
    (hvertices : ∀ x : EuclideanSpace ℝ (Fin n),
      IsVertex P x ↔ ∃ i : Fin N, v i = x)
    (hcontained : P ⊆ unitBall n) :
    (MeasureTheory.volume P).toReal /
        (MeasureTheory.volume (unitBall n)).toReal ≤
      ((3 : ℝ) * Real.sqrt (Real.log (N : ℝ) / (n : ℝ))) ^ n := by
  have _hHullContained : finiteConvexHull v ⊆ unitBall n :=
    finiteConvexHull_subset_unitBall n N P v hpolytope hcontained
  have hratio : (MeasureTheory.volume P).toReal /
      (MeasureTheory.volume (unitBall n)).toReal ≤ 1 :=
    contained_volume_ratio_le_one n P hcontained
  by_cases htrivial : 1 ≤
      ((3 : ℝ) * Real.sqrt (Real.log (N : ℝ) / (n : ℝ))) ^ n
  · exact le_trans hratio htrivial
  · subst P
    by_cases h : N = 1
    · subst N
      rw [finiteConvexHull_one]
      haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
      simp
    · have htwo : 2 ≤ N := by omega
      sorry

end PolytopeVolumeBound
