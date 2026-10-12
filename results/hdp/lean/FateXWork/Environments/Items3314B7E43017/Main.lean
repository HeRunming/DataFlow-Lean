import Mathlib

open MeasureTheory

namespace Rademacher

abbrev Cube (n : ℕ) := Fin n → Bool

def cubePoint {n : ℕ} (x : Cube n) : Fin n → ℝ :=
  fun i => if x i = true then (1 : ℝ) else (-1 : ℝ)

def RademacherCoordinate {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (f : Ω → ℝ) : Prop :=
  Measurable f ∧
    μ {ω : Ω | f ω = (-1 : ℝ)} = (1 : ENNReal) / (2 : ENNReal) ∧
    μ {ω : Ω | f ω = (1 : ℝ)} = (1 : ENNReal) / (2 : ENNReal)

def RademacherRandomVector {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (X : Ω → Fin n → ℝ) : Prop :=
  (∀ i : Fin n, RademacherCoordinate μ (fun ω : Ω => X ω i)) ∧
    ∀ (s : Finset (Fin n)) (a : Fin n → ℝ),
      μ {ω : Ω | ∀ i ∈ s, X ω i = a i} =
        Finset.prod s (fun i : Fin n =>
          (μ {ω : Ω | X ω i = a i} : ENNReal))

def UniformOnCube {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (X : Ω → Fin n → ℝ) : Prop :=
  (∀ i : Fin n, Measurable (fun ω : Ω => X ω i)) ∧
    ∀ x : Cube n,
      μ {ω : Ω | X ω = cubePoint x} =
        (1 : ENNReal) / (Fintype.card (Cube n) : ENNReal)

def Isotropic {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (μ : MeasureTheory.Measure Ω) (X : Ω → Fin n → ℝ) : Prop :=
  ∀ i j : Fin n,
    (∫ ω : Ω, X ω i * X ω j ∂μ) =
      if i = j then (1 : ℝ) else (0 : ℝ)

private theorem rademacher_to_uniform {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → Fin n → ℝ) (h : RademacherRandomVector μ X) : UniformOnCube μ X := by
  refine ⟨fun i => (h.1 i).1, ?_⟩
  intro x
  have he : {ω | X ω = cubePoint x} = {ω | ∀ i ∈ (Finset.univ : Finset (Fin n)), X ω i = cubePoint x i} := by
    ext ω
    simp [funext_iff]
  rw [he, h.2]
  have hc (i : Fin n) : μ {ω | X ω i = cubePoint x i} = (1 : ENNReal) / 2 := by
    unfold cubePoint
    split_ifs
    · exact (h.1 i).2.2
    · exact (h.1 i).2.1
  simp_rw [hc]
  simp [Fintype.card_bool, ENNReal.inv_pow]

private theorem fiber_coord_mem {Ω : Type*} {n : ℕ} (X : Ω → Fin n → ℝ)
    (i : Fin n) (x : Cube n) (ω : Ω)
    (hω : X ω = cubePoint x) :
    X ω i = if x i = true then (1 : ℝ) else -1 := by
  exact congrFun hω i

private theorem cubePoint_injective {n : ℕ} :
    Function.Injective (cubePoint : Cube n → (Fin n → ℝ)) := by
  intro x y h
  funext i
  cases hx : x i <;> cases hy : y i
  · simpa [hx, hy]
  · have hi := congrFun h i
    norm_num [cubePoint, hx, hy] at hi
  · have hi := congrFun h i
    norm_num [cubePoint, hx, hy] at hi
  · simpa [hx, hy]

private theorem uniform_to_rademacher_of_components {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (X : Ω → Fin n → ℝ)
    (hcoord : ∀ i : Fin n, RademacherCoordinate μ (fun ω => X ω i))
    (hcyl : ∀ (s : Finset (Fin n)) (a : Fin n → ℝ),
      μ {ω | ∀ i ∈ s, X ω i = a i} =
        ∏ i ∈ s, μ {ω | X ω i = a i}) :
    RademacherRandomVector μ X := by
  exact ⟨hcoord, hcyl⟩

private theorem cube_fiber_measurable_of_coordinate_measurable {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (X : Ω → Fin n → ℝ)
    (hm : ∀ i : Fin n, Measurable (fun ω => X ω i)) (x : Cube n) :
    MeasurableSet {ω | X ω = cubePoint x} := by
  have hX : Measurable X := measurable_pi_lambda _ hm
  exact (MeasurableSet.singleton _).preimage hX

private theorem finite_cube_union_measure {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → Fin n → ℝ) (hm : ∀ i : Fin n, Measurable (fun ω => X ω i))
    (hu : ∀ x : Cube n, μ {ω | X ω = cubePoint x} =
      (1 : ENNReal) / (Fintype.card (Cube n) : ENNReal))
    (S : Finset (Cube n)) :
    μ (⋃ x ∈ S, {ω | X ω = cubePoint x}) =
      (S.card : ENNReal) / (Fintype.card (Cube n) : ENNReal) := by
  classical
  have hmeas (x : Cube n) : MeasurableSet {ω | X ω = cubePoint x} :=
    cube_fiber_measurable_of_coordinate_measurable X hm x
  have hd : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → Disjoint {ω | X ω = cubePoint x} {ω | X ω = cubePoint y} := by
    intro x hx y hy hxy
    apply Set.disjoint_left.2
    intro ω hxω hyω
    apply hxy
    apply cubePoint_injective
    exact hxω.symm.trans hyω
  rw [measure_biUnion_finset (μ := μ) (s := S) (f := fun x => {ω | X ω = cubePoint x}) hd
    (fun b hb => hmeas b)]
  simp_rw [hu]
  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [Fintype.card_fun, Fintype.card_bool]
  norm_num [ENNReal.div_eq_inv_mul, mul_comm]

theorem rademacher_iff_uniform {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (X : Ω → Fin n → ℝ) :
    RademacherRandomVector μ X ↔ UniformOnCube μ X := by sorry

theorem rademacher_isotropic {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (X : Ω → Fin n → ℝ)
    (hX : RademacherRandomVector μ X) :
    Isotropic μ X := by sorry

end Rademacher
