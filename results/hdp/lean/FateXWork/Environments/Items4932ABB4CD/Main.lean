import Mathlib

noncomputable section

inductive WalshIndex : Nat → Type
  | base (i : Fin 2) : WalshIndex 1
  | left {k : Nat} (i : WalshIndex (k + 1)) : WalshIndex ((k + 1) + 1)
  | right {k : Nat} (i : WalshIndex (k + 1)) : WalshIndex ((k + 1) + 1)

instance walshIndexDecidableEq (k : Nat) : DecidableEq (WalshIndex (k + 1)) := by
  sorry

instance walshIndexFintype (k : Nat) : Fintype (WalshIndex (k + 1)) := by
  sorry

def walshBase : Matrix (WalshIndex 1) (WalshIndex 1) ℝ :=
  fun i j =>
    match i, j with
    | WalshIndex.base i, WalshIndex.base j =>
        if i = (1 : Fin 2) ∧ j = (1 : Fin 2) then
          (-1 : ℝ)
        else
          (1 : ℝ)

def walshBlock {k : Nat}
    (A : Matrix (WalshIndex (k + 1)) (WalshIndex (k + 1)) ℝ) :
    Matrix (WalshIndex ((k + 1) + 1)) (WalshIndex ((k + 1) + 1)) ℝ :=
  fun i j =>
    match i, j with
    | WalshIndex.left i, WalshIndex.left j => A i j
    | WalshIndex.left i, WalshIndex.right j => A i j
    | WalshIndex.right i, WalshIndex.left j => A i j
    | WalshIndex.right i, WalshIndex.right j => -A i j

def IsOrthogonalMatrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) : Prop :=
  ∀ i j : ι,
    ((∑ q : ι, A i q * A j q) : ℝ) =
      if i = j then (1 : ℝ) else (0 : ℝ)

theorem walsh_matrices_are_orthogonal
    (W : ∀ k : Nat, Matrix (WalshIndex (k + 1)) (WalshIndex (k + 1)) ℝ)
    (hW1 : W 0 = walshBase)
    (hWsucc : ∀ k : Nat, W (k + 1) = walshBlock (W k)) :
    ∀ k : Nat,
      IsOrthogonalMatrix
        (fun i j =>
          W k i j /
            Real.sqrt (Fintype.card (WalshIndex (k + 1)) : ℝ)) := by
  sorry
