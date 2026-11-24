import LoweringFixtures.Common

/-! A copy of an unassigned cell one row past the usable rows (k = 4: 9 usable): Rust's keygen
`copy` fails with NotEnoughRowsAvailable, Lean must reject too. -/
namespace LoweringFixtures.CopyPastUsable
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let inst ← instanceColumn
  enableEquality ⟨.advice, a⟩
  enableEquality ⟨.instance, inst⟩

def source : CS := (configure.run {}).2

def fixture : Export.Replay.Fixture where
  source := source
  k := 4
  ops := [
    .region "r0" [.assignAdvice ⟨0⟩ 0 witness, .assignAdvice ⟨0⟩ 1 witness],
    .region "r1" [.assignAdvice ⟨0⟩ 0 witness, .constrainEqual (cell 1 0 .advice 0) (cell 0 9 .advice 0)]]

end LoweringFixtures.CopyPastUsable
