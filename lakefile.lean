import Lake
open Lake DSL

package Clean where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩]
  -- consumers that pin a release tag download the prebuilt `Clean` library attached to that
  -- release (see `.github/workflows/release-tag.yml`) instead of compiling it
  preferReleaseBuild := true
  releaseRepo := "https://github.com/Verified-zkEVM/clean"
  -- one archive for all platforms, see `platformIndependent` below
  buildArchive := "Clean-oleans.tar.gz"
  -- a release archive only works with the toolchain it was built with
  fixedToolchain := true

@[default_target]
lean_lib Clean where
  -- every file under `Clean/` that Lake builds uses the module system; warn if a new one does not
  requiresModuleSystem := true
  -- leave platform-dependent elements out of module traces, so oleans built on Linux CI
  -- validate on every platform
  platformIndependent := true

lean_lib CleanTests where
  roots := #[`Clean.Test, `Clean.Specs.BLAKE3.ChunkProcessingTests]

lean_exe export_fibonacci_ensemble_rust where
  root := `Clean.Examples.FibonacciVm.Rust

lean_exe export_femtocairo_flat_air_rust where
  root := `Clean.Examples.FemtoCairo.FlatAirRust

lean_exe export_opcode_vm_rust where
  root := `Clean.Examples.OpcodeVm.Rust

lean_exe export_squares_table_rust where
  root := `Clean.Examples.SquaresTable.Rust

lean_exe export_witness_ir_reference_rust where
  root := `Clean.Backends.Plonky3.Test.Reference

lean_exe export_differential_rust where
  root := `Clean.Backends.Plonky3.Test.Differential

require "leanprover-community" / "mathlib" @ git "v4.35.0"
require CompPoly from git "https://github.com/Verified-zkEVM/CompPoly.git" @ "v4.35.0"
