import Lake
open Lake DSL

package Clean where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩]

@[default_target]
lean_lib Clean where

lean_lib CleanTests where
  roots := #[`Clean.Test, `Clean.Specs.BLAKE3.ChunkProcessingTests]

lean_exe export_fibonacci_ensemble_rust where
  root := `Clean.Examples.FibonacciVm.EnsembleRust

lean_exe export_femtocairo_flat_air_rust where
  root := `Clean.Examples.FemtoCairo.FlatAirRust

require mathlib from git "https://github.com/leanprover-community/mathlib4"@"v4.32.2"
