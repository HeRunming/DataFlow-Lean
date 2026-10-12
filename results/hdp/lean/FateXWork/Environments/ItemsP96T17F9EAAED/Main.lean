import Mathlib

universe u

/-- A real-valued positive semidefinite kernel. -/
def IsPositiveSemidefiniteKernel {α : Type u} (K : α → α → ℝ) : Prop :=
  (∀ x y : α, K x y = K y x) ∧
    (∀ {n : ℕ} (x : Fin n → α) (coeff : Fin n → ℝ),
      (0 : ℝ) ≤
        (∑ i : Fin n,
          (∑ j : Fin n, coeff i * coeff j * K (x i) (x j) : ℝ) : ℝ))

/-- Existence of a real Hilbert-space feature representation of a kernel. -/
def HasHilbertSpaceKernelRepresentation {α : Type u} (K : α → α → ℝ) : Prop :=
  ∃ (H : Type*),
    ∃ (instN : NormedAddCommGroup H),
      ∃ (instIP : InnerProductSpace ℝ H),
        ∃ (instC : CompleteSpace H),
          ∃ (φ : α → H),
            (let _ := instN
             let _ := instIP
             let _ := instC
             ∀ x y : α, K x y = inner ℝ (φ x) (φ y))

private theorem zero_kernel_psd {α : Type u} :
    IsPositiveSemidefiniteKernel (fun _ _ : α => (0 : ℝ)) := by
  unfold IsPositiveSemidefiniteKernel
  constructor
  · intro x y
    rfl
  · intro n x coeff
    simp

/-- The representation direction of Moore-Aronszajn. -/
private theorem representation_is_psd
    {α : Type u} (K : α → α → ℝ) :
    HasHilbertSpaceKernelRepresentation K → IsPositiveSemidefiniteKernel K := by
  rintro ⟨H, instN, instIP, instC, φ, hφ⟩
  letI : NormedAddCommGroup H := instN
  letI : InnerProductSpace ℝ H := instIP
  letI : CompleteSpace H := instC
  constructor
  · intro x y
    rw [hφ x y, hφ y x]
    exact real_inner_comm _ _
  · intro n x coeff
    let z : H := ∑ i, coeff i • φ (x i)
    have hz : 0 ≤ inner ℝ z z := real_inner_self_nonneg
    have hEq : (∑ i : Fin n, ∑ j : Fin n,
        coeff i * coeff j * K (x i) (x j)) = inner ℝ z z := by
      simp only [z, hφ, sum_inner, inner_sum, real_inner_smul_left,
        real_inner_smul_right, mul_assoc]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [real_inner_comm (φ (x i)) (φ (x j))]
    rw [hEq]
    exact hz

/-- A negative kernel cannot have a Hilbert-space representation. -/
private theorem no_rep_neg_kernel :
    ¬ HasHilbertSpaceKernelRepresentation (fun _ _ : PUnit => (-1 : ℝ)) := by
  intro h
  have hp := representation_is_psd (fun _ _ : PUnit => (-1 : ℝ)) h
  have hq := hp.2 (x := fun _ : Fin 1 => PUnit.unit) (coeff := fun _ => 1)
  norm_num at hq

/-- Moore-Aronszajn characterization of positive semidefinite kernels. -/
theorem moore_aronszajn_theorem
    {α : Type u} (K : α → α → ℝ) :
    HasHilbertSpaceKernelRepresentation K ↔
      IsPositiveSemidefiniteKernel K := by
  constructor
  · exact representation_is_psd K
  · sorry

/-- Mercer characterization of positive semidefinite kernels. -/
theorem mercer_theorem
    {α : Type u} (K : α → α → ℝ) :
    HasHilbertSpaceKernelRepresentation K ↔
      IsPositiveSemidefiniteKernel K := by
  exact moore_aronszajn_theorem K
