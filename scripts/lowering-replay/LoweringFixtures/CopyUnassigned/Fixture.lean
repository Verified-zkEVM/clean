import LoweringFixtures.Common

/-! `constrain_equal` from an assigned advice cell to one nothing assigns, in the same region and
past its last row. Rust keys it (keygen.rs:142-154 checks only columns and usable rows), its
prover reading 0 there; so does Lean. -/
namespace LoweringFixtures.CopyUnassigned
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let b ← adviceColumn
  enableEquality ⟨.advice, a⟩
  enableEquality ⟨.advice, b⟩

def source : CS := (configure.run {}).2

def fixture : Export.Replay.Fixture where
  source := source
  k := 5
  ops := [.region "r" [.assignAdvice ⟨0⟩ 0 witness, .assignAdvice ⟨0⟩ 1 witness,
    .constrainEqual (cell 0 0 .advice 0) (cell 0 0 .advice 1),
    .constrainEqual (cell 0 1 .advice 0) (cell 0 3 .advice 1)],
    .region "next" [.assignAdvice ⟨1⟩ 0 witness]]

end LoweringFixtures.CopyUnassigned
