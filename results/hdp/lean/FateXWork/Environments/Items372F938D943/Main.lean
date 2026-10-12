import Mathlib

open scoped BigOperators

noncomputable section

namespace TensorSpecialization

/-- An order-`order` tensor with a separately specified size for each axis. -/
def BookTensor (order : ℕ) (dims : Fin order → ℕ) : Type :=
  ((k : Fin order) → Fin (dims k)) → ℝ

/-- The entrywise tensor inner product. -/
def tensorInnerProduct {order : ℕ} {dims : Fin order → ℕ}
    (A B : BookTensor order dims) : ℝ :=
  (∑ idx : ((k : Fin order) → Fin (dims k)), A idx * B idx : ℝ)

def vectorInnerProduct {n : ℕ} (v w : Fin n → ℝ) : ℝ :=
  (∑ i : Fin n, v i * w i : ℝ)

def matrixInnerProduct {rows cols : ℕ}
    (A B : Matrix (Fin rows) (Fin cols) ℝ) : ℝ :=
  (∑ i : Fin rows, (∑ j : Fin cols, A i j * B i j : ℝ) : ℝ)

def vectorAsTensor {n : ℕ} (v : Fin n → ℝ) :
    BookTensor 1 (fun _ : Fin 1 => n) :=
  fun idx => v (idx (0 : Fin 1))

def matrixShape (rows cols : ℕ) : Fin 2 → ℕ :=
  Fin.cases rows (fun _ : Fin 1 => cols)

def matrixAsTensor {rows cols : ℕ}
    (A : Matrix (Fin rows) (Fin cols) ℝ) :
    BookTensor 2 (matrixShape rows cols) :=
  fun idx => A (idx (0 : Fin 2)) (idx (1 : Fin 2))

/-- Vectors identify bijectively with order-one tensors. -/
theorem vectors_are_order_one_tensors (n : ℕ) :
    Function.Bijective (vectorAsTensor (n := n)) := by sorry

/-- Rectangular matrices identify bijectively with order-two tensors. -/
theorem matrices_are_order_two_tensors (rows cols : ℕ) :
    Function.Bijective (matrixAsTensor (rows := rows) (cols := cols)) := by sorry

/-- The tensor inner product specializes to the vector inner product. -/
theorem tensor_innerProduct_order_one (n : ℕ) (v w : Fin n → ℝ) :
    tensorInnerProduct (vectorAsTensor v) (vectorAsTensor w) =
      vectorInnerProduct v w := by sorry

/-- The tensor inner product specializes to the matrix inner product. -/
theorem tensor_innerProduct_order_two (rows cols : ℕ)
    (A B : Matrix (Fin rows) (Fin cols) ℝ) :
    tensorInnerProduct (matrixAsTensor A) (matrixAsTensor B) =
      matrixInnerProduct A B := by sorry

end TensorSpecialization
