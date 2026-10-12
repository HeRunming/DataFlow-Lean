import Mathlib.LinearAlgebra.Matrix.PosDef

namespace Source

/-- A real square matrix is symmetric positive semidefinite when it is symmetric
and positive semidefinite. -/
def SymmetricPositiveSemidefinite {n : Type*} (X : Matrix n n ℝ) : Prop :=
  X.IsSymm ∧ X.PosSemidef

/-- `X ⪰ 0` means that `X` is symmetric positive semidefinite. -/
def SucceqZero {n : Type*} (X : Matrix n n ℝ) : Prop :=
  SymmetricPositiveSemidefinite X

/-- `X ⪰ Y` means that `X - Y` is symmetric positive semidefinite. -/
def Succeq {n : Type*} (X Y : Matrix n n ℝ) : Prop :=
  SymmetricPositiveSemidefinite (X - Y)

/-- `Y ⪯ X` means that `X - Y` is symmetric positive semidefinite. -/
def Preceq {n : Type*} (X Y : Matrix n n ℝ) : Prop :=
  SymmetricPositiveSemidefinite (Y - X)

theorem succeq_zero_iff {n : Type*} (X : Matrix n n ℝ) :
    SucceqZero X ↔ SymmetricPositiveSemidefinite X := by
  set_option maxHeartbeats 5000 in
    first | (rfl; done) | (assumption; done) | (simp; done) | (norm_num; done) | (omega; done) | (linarith; done) | (ring; done) | (simp_all [SymmetricPositiveSemidefinite, SucceqZero, Succeq, Preceq]; done)

theorem succeq_iff_preceq {n : Type*} (X Y : Matrix n n ℝ) :
    Succeq X Y ↔ Preceq Y X := by
  set_option maxHeartbeats 5000 in
    first | (rfl; done) | (assumption; done) | (simp; done) | (norm_num; done) | (omega; done) | (linarith; done) | (ring; done) | (simp_all [SymmetricPositiveSemidefinite, SucceqZero, Succeq, Preceq]; done)

end Source
