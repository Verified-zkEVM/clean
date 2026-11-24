import LoweringFixtures.Common

/-! Rust's region arithmetic is `usize` and wraps in a release build (no overflow checks):
region 1 starts at 2, so its enable and its cell at offset `2^64 - 1` land on row 1, and the
shape's `offset + 1` wraps to 0, so the row count stays 1. Rust keys it under both planners; Lean
lowers in `usize` too (`Usize`). -/
namespace LoweringFixtures.PlacementWrap
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  enableEquality ⟨.advice, a⟩
  let q ← selector
  gate "g" q do
    let x ← advice a
    return #[("g", x)]

def source : CS := (configure.run {}).2

def g : GateSpec := source.gates[0]?.getD ⟨"", ⟨0, true⟩, #[], #[], false, false⟩

def wrap : Nat := 2 ^ 64 - 1

def fixture : Export.Replay.Fixture where
  source := source
  k := 4
  ops := [
    .region "r0" [.assignAdvice ⟨0⟩ 0 witness, .assignAdvice ⟨0⟩ 1 witness],
    .region "r1" [.assignAdvice ⟨0⟩ 0 witness, .enableGate (cleanGate g) wrap,
      .constrainEqual (cell 1 wrap .advice 0) (cell 0 0 .advice 0)]]

end LoweringFixtures.PlacementWrap
