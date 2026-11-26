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

@[default_target]
lean_lib Halo2 where
  roots := #[`Clean.Halo2]
  requiresModuleSystem := true
  platformIndependent := true

lean_lib CleanTests where
  roots := #[`Clean.Test, `Clean.Specs.BLAKE3.ChunkProcessingTests]
  requiresModuleSystem := true

lean_exe export_fibonacci_ensemble_rust where
  root := `Clean.Examples.FibonacciVm.Rust

lean_exe export_femtocairo_flat_air_rust where
  root := `Clean.Examples.FemtoCairo.FlatAirRust

lean_exe export_opcode_vm_rust where
  root := `Clean.Examples.OpcodeVm.Rust

lean_exe export_witness_ir_reference_rust where
  root := `Clean.Backends.Plonky3.Test.Reference

lean_exe export_differential_rust where
  root := `Clean.Backends.Plonky3.Test.Differential

-- The shared elliptic-curve/finite-field theory used by Clean/Ironwood: the Lean 4.35 port of
-- daira/CompElliptic, on the bot fork. Brings CompPoly transitively.
require CompElliptic from git
  "https://github.com/mitschabaude-bot/CompElliptic.git" @ "68211e1113172c77ae7c61c70f1048fd82684b0c"

require "leanprover-community" / "mathlib" @ git "v4.35.0"
require CompPoly from git "https://github.com/Verified-zkEVM/CompPoly.git" @ "v4.35.0"
