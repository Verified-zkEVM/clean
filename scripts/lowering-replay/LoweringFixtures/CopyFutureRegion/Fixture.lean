import LoweringFixtures.Common

/-! A region copies a cell of a later region. Rust's `constrain_equal` indexes `regions` with the
cell's region (single_pass.rs), which does not exist yet, and panics; Lean must reject. -/
namespace LoweringFixtures.CopyFutureRegion
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  enableEquality ⟨.advice, a⟩

def source : CS := (configure.run {}).2

def fixture : Export.Replay.Fixture where
  source := source
  k := 4
  ops := [
    .region "r0" [.assignAdvice ⟨0⟩ 0 witness, .constrainEqual (cell 0 0 .advice 0) (cell 1 0 .advice 0)],
    .region "r1" [.assignAdvice ⟨0⟩ 0 witness]]

end LoweringFixtures.CopyFutureRegion
