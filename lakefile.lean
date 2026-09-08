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

lean_exe export_backend_test_data where
  root := `Clean.Air.Extraction.TestData

require "leanprover-community" / "mathlib" @ git "v4.33.1"
