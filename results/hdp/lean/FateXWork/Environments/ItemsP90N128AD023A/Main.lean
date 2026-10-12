import Mathlib

noncomputable section

def oppositeLabelSum {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : ℝ :=
  ((∑ i : Fin n, ∑ j : Fin n,
      if x i * x j = (-1 : ℝ) then A i j else (0 : ℝ)) : ℝ)

def pairLabelSum {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : ℝ :=
  ((∑ i : Fin n, ∑ j : Fin n,
      A i j * ((1 : ℝ) - x i * x j)) : ℝ)

def cut {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : ℝ :=
  (1 / 2 : ℝ) * oppositeLabelSum A x

theorem cut_eq_quarter_sum {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ)
    (hlabels : ∀ i : Fin n, x i = (-1 : ℝ) ∨ x i = (1 : ℝ)) :
    cut A x =
      (1 / 4 : ℝ) *
        ((∑ i : Fin n, ∑ j : Fin n,
            A i j * ((1 : ℝ) - x i * x j)) : ℝ) := by
  unfold cut oppositeLabelSum
  have hterm : ∀ i j : Fin n,
      (if x i * x j = (-1 : ℝ) then A i j else 0) =
        (1 / 2 : ℝ) * (A i j * ((1 : ℝ) - x i * x j)) := by
    intro i j
    rcases hlabels i with hi | hi <;> rcases hlabels j with hj | hj
    all_goals norm_num [hi, hj] <;> ring
  simp_rw [hterm]
  simp only [← Finset.mul_sum]
  ring

def maxcut {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  (1 / 4 : ℝ) * sSup
    {v : ℝ |
      ∃ x : Fin n → ℝ,
        (∀ i : Fin n, x i = (-1 : ℝ) ∨ x i = (1 : ℝ)) ∧
          v = ((∑ i : Fin n, ∑ j : Fin n,
            A i j * ((1 : ℝ) - x i * x j)) : ℝ)}

theorem maxcut_eq_label_max {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    maxcut A =
      (1 / 4 : ℝ) * sSup
        {v : ℝ |
          ∃ x : Fin n → ℝ,
            (∀ i : Fin n, x i = (-1 : ℝ) ∨ x i = (1 : ℝ)) ∧
              v = ((∑ i : Fin n, ∑ j : Fin n,
                A i j * ((1 : ℝ) - x i * x j)) : ℝ)} := by
  rfl
