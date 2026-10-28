import Lake
open Lake DSL

package Clean where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩]

@[default_target]
lean_lib Clean where
  -- every file under `Clean/` that Lake builds uses the module system; warn if a new one does not
  requiresModuleSystem := true

lean_lib CleanTests where
  roots := #[`Clean.Test, `Clean.Specs.BLAKE3.ChunkProcessingTests]

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

require "leanprover-community" / "mathlib" @ git "v4.33.1"
require CompPoly from git "https://github.com/Verified-zkEVM/CompPoly.git"@"0804bcc83cd98f5f3e933adc6783aa99dacdedc1"
