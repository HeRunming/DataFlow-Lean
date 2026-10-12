import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Order.Filter.Basic

open scoped BigOperators

namespace SemidefiniteProgramming

def matrixInner {n : Nat} (A X : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ((∑ i : Fin n, ((∑ j : Fin n, (A i j * X i j : ℝ)) : ℝ)) : ℝ)

def SymmetricPosSemidef {n : Nat} (X : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  X.transpose = X ∧ Matrix.PosSemidef X

def SDPFeasibleLE {n N : Nat}
    (B : Fin N → Matrix (Fin n) (Fin n) ℝ)
    (b : Fin N → ℝ)
    (X : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  SymmetricPosSemidef X ∧
    ∀ i : Fin N, matrixInner (B i) X ≤ b i

def SDPFeasibleGE {n N : Nat}
    (B : Fin N → Matrix (Fin n) (Fin n) ℝ)
    (b : Fin N → ℝ)
    (X : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  SymmetricPosSemidef X ∧
    ∀ i : Fin N, matrixInner (B i) X ≥ b i

def SDPFeasibleEQ {n N : Nat}
    (B : Fin N → Matrix (Fin n) (Fin n) ℝ)
    (b : Fin N → ℝ)
    (X : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  SymmetricPosSemidef X ∧
    ∀ i : Fin N, matrixInner (B i) X = b i

def SDPMaximizationLE {n N : Nat}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (B : Fin N → Matrix (Fin n) (Fin n) ℝ)
    (b : Fin N → ℝ)
    (X : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  IsMaxOn (fun Y : Matrix (Fin n) (Fin n) ℝ => matrixInner A Y)
    {Y : Matrix (Fin n) (Fin n) ℝ | SDPFeasibleLE B b Y} X

def SDPMinimizationLE {n N : Nat}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (B : Fin N → Matrix (Fin n) (Fin n) ℝ)
    (b : Fin N → ℝ)
    (X : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  IsMinOn (fun Y : Matrix (Fin n) (Fin n) ℝ => matrixInner A Y)
    {Y : Matrix (Fin n) (Fin n) ℝ | SDPFeasibleLE B b Y} X

def SDPMaximizationGE {n N : Nat}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (B : Fin N → Matrix (Fin n) (Fin n) ℝ)
    (b : Fin N → ℝ)
    (X : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  IsMaxOn (fun Y : Matrix (Fin n) (Fin n) ℝ => matrixInner A Y)
    {Y : Matrix (Fin n) (Fin n) ℝ | SDPFeasibleGE B b Y} X

def SDPMinimizationGE {n N : Nat}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (B : Fin N → Matrix (Fin n) (Fin n) ℝ)
    (b : Fin N → ℝ)
    (X : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  IsMinOn (fun Y : Matrix (Fin n) (Fin n) ℝ => matrixInner A Y)
    {Y : Matrix (Fin n) (Fin n) ℝ | SDPFeasibleGE B b Y} X

def SDPMaximizationEQ {n N : Nat}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (B : Fin N → Matrix (Fin n) (Fin n) ℝ)
    (b : Fin N → ℝ)
    (X : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  IsMaxOn (fun Y : Matrix (Fin n) (Fin n) ℝ => matrixInner A Y)
    {Y : Matrix (Fin n) (Fin n) ℝ | SDPFeasibleEQ B b Y} X

def SDPMinimizationEQ {n N : Nat}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (B : Fin N → Matrix (Fin n) (Fin n) ℝ)
    (b : Fin N → ℝ)
    (X : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  IsMinOn (fun Y : Matrix (Fin n) (Fin n) ℝ => matrixInner A Y)
    {Y : Matrix (Fin n) (Fin n) ℝ | SDPFeasibleEQ B b Y} X

theorem matrixInner_eq_trace {n : Nat}
    (A X : Matrix (Fin n) (Fin n) ℝ) :
    matrixInner A X = Matrix.trace (A.transpose * X) := by
  classical
  unfold matrixInner Matrix.trace
  rw [Finset.sum_comm]
  simp [Matrix.mul_apply]

theorem semidefinite_program_maximization_formulation {n N : Nat}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (B : Fin N → Matrix (Fin n) (Fin n) ℝ)
    (b : Fin N → ℝ) :
    ∃ objective : Matrix (Fin n) (Fin n) ℝ → ℝ,
      objective = (fun X : Matrix (Fin n) (Fin n) ℝ => matrixInner A X) ∧
      ∃ constraints : Matrix (Fin n) (Fin n) ℝ → Prop,
        constraints = (SDPFeasibleLE B b) ∧
        ∀ X : Matrix (Fin n) (Fin n) ℝ,
          constraints X ↔
            (SymmetricPosSemidef X ∧
              ∀ i : Fin N, matrixInner (B i) X ≤ b i) := by
  refine ⟨fun X => matrixInner A X, rfl, SDPFeasibleLE B b, rfl, ?_⟩
  intro X
  rfl

end SemidefiniteProgramming
