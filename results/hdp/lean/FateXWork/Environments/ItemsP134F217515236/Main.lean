import Mathlib

/--
Source proof: The source applies the law of large numbers to each entry of `Σ` and
then takes the almost-sure intersection over the finitely many entries.
Proof sketch: use finiteness of the matrix index type to combine the coordinatewise
a.e. convergence statements and the finite-function convergence criterion.
Prover notes: the source leaves the dimensions, probability space, and scalar
field implicit; these are made explicit here as a finite index type, a measure,
and real-valued matrices. The entrywise hypotheses stand for the cited LLN step.
-/
theorem matrix_tendsto_ae_of_entrywise
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : MeasureTheory.Measure Ω)
    (sigmaM : ℕ → Ω → Matrix ι ι ℝ) (sigma : Ω → Matrix ι ι ℝ)
    (h : ∀ i j, ∀ᵐ ω ∂μ, Filter.Tendsto (fun m => sigmaM m ω i j) Filter.atTop (nhds (sigma ω i j))) :
    ∀ᵐ ω ∂μ, Filter.Tendsto (fun m => sigmaM m ω) Filter.atTop (nhds (sigma ω)) := by
  sorry
