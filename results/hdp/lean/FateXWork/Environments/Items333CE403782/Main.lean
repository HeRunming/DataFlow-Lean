import Mathlib

open scoped BigOperators
open MeasureTheory

namespace RotationInvariantSubgaussian

def dotFin {n : ℕ} (x y : Fin n → ℝ) : ℝ :=
  ((∑ i : Fin n, x i * y i) : ℝ)

def IsOrthogonalMatrix {n : ℕ} (U : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ i j : Fin n,
    dotFin (U i) (U j) = if i = j then (1 : ℝ) else (0 : ℝ)

noncomputable def scalarPsiTwoNorm {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Y : Ω → ℝ) : ℝ :=
  sInf {K : ℝ |
    (0 : ℝ) < K ∧
      ((∫ ω, Real.exp ((Y ω) ^ 2 / K ^ 2) ∂P) : ℝ) ≤ (2 : ℝ)}

noncomputable def psiTwoNorm {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (P : Measure Ω) (X : Ω → Fin n → ℝ) : ℝ :=
  sSup {r : ℝ |
    ∃ coeff : Fin n → ℝ,
      (((∑ i : Fin n, (coeff i) ^ 2) : ℝ) = (1 : ℝ)) ∧
        r = scalarPsiTwoNorm P (fun ω => dotFin (X ω) coeff)}

def IsSubgaussianVector {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (P : Measure Ω) (X : Ω → Fin n → ℝ) : Prop :=
  Measurable X ∧
    ∀ coeff : Fin n → ℝ,
      ∃ K : ℝ,
        (0 : ℝ) < K ∧
          Integrable (fun ω => dotFin (X ω) coeff) P ∧
            ((∫ ω, Real.exp ((dotFin (X ω) coeff) ^ 2 / K ^ 2) ∂P) : ℝ) ≤ (2 : ℝ)

private lemma dotFin_mulVec {n : ℕ} (U : Matrix (Fin n) (Fin n) ℝ) (x c : Fin n → ℝ) :
    dotFin (U.mulVec x) c = dotFin x (fun j => ∑ i, U i j * c i) := by
  simp only [dotFin, Matrix.mulVec, dotProduct]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

private lemma orthogonal_left_inverse {n : ℕ} (U : Matrix (Fin n) (Fin n) ℝ)
    (hU : IsOrthogonalMatrix U) : U * U.transpose = 1 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply]
  rw [show (∑ x, U i x * U j x) = dotFin (U i) (U j) by rfl]
  rw [hU]

private lemma orthogonal_right_inverse {n : ℕ} (U : Matrix (Fin n) (Fin n) ℝ)
    (hU : IsOrthogonalMatrix U) : U.transpose * U = 1 := by
  have h := orthogonal_left_inverse U hU
  exact (Matrix.mul_eq_one_comm.mp h)

private lemma orthogonal_mulVec_dot {n : ℕ} (V : Matrix (Fin n) (Fin n) ℝ)
    (hV : IsOrthogonalMatrix V) (x y : Fin n → ℝ) :
    dotFin (V.mulVec x) (V.mulVec y) = dotFin x y := by
  rw [dotFin_mulVec]
  have hv : (fun j => ∑ i, V i j * (V.mulVec y) i) = y := by
    change V.transpose.mulVec (V.mulVec y) = y
    rw [Matrix.mulVec_mulVec]
    rw [orthogonal_right_inverse V hV]
    simp
  rw [hv]

theorem subgaussian_mulVec_rotation_invariant
    {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Matrix (Fin n) (Fin n) ℝ)
    (X : Ω → Fin n → ℝ)
    (hU : IsOrthogonalMatrix U)
    (hX : IsSubgaussianVector P X) :
    IsSubgaussianVector P (fun ω => U.mulVec (X ω)) ∧
      psiTwoNorm P (fun ω => U.mulVec (X ω)) = psiTwoNorm P X := by
  classical
  rcases hX with ⟨hXm, hX⟩
  constructor
  · constructor
    · fun_prop
    · intro c
      let d : Fin n → ℝ := fun j => ∑ i, U i j * c i
      obtain ⟨K, hK, hI, hE⟩ := hX d
      refine ⟨K, hK, ?_, ?_⟩
      · simpa [dotFin_mulVec, d] using hI
      · simpa [dotFin_mulVec, d] using hE
  · simp only [psiTwoNorm]
    apply congrArg sSup
    ext r
    constructor
    · rintro ⟨c, hc, rfl⟩
      let d : Fin n → ℝ := fun j => ∑ i, U i j * c i
      have hd : U.mulVec d = c := by
        change U.mulVec (U.transpose.mulVec c) = c
        rw [Matrix.mulVec_mulVec, orthogonal_left_inverse U hU]
        simp
      have hnorm : (∑ i, d i ^ 2) = ∑ i, c i ^ 2 := by
        have hh := orthogonal_mulVec_dot U hU d d
        rw [hd] at hh
        simpa [dotFin, pow_two, mul_comm] using hh.symm
      refine ⟨d, hnorm.trans hc, ?_⟩
      simp [d, dotFin_mulVec]
    · rintro ⟨c, hc, rfl⟩
      let d : Fin n → ℝ := U.mulVec c
      have hnorm : (∑ i, d i ^ 2) = ∑ i, c i ^ 2 := by
        simpa [d, dotFin, pow_two, mul_comm] using orthogonal_mulVec_dot U hU c c
      refine ⟨d, hnorm.trans hc, ?_⟩
      simp [d, orthogonal_mulVec_dot U hU]

end RotationInvariantSubgaussian
