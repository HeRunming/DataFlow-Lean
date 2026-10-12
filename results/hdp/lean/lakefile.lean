import Lake
open Lake DSL

-- Formalization results for High-Dimensional Probability (Vershynin), produced by
-- the LeanFlow campaign described in ../README.md. Only Mathlib is required.
package «hdp_results» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`pp.proofs.withType, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.28.0"

@[default_target]
lean_lib FateXWork where
