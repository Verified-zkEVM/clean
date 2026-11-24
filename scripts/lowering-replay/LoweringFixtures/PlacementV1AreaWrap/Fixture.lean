import LoweringFixtures.Common

/-! V1's sort key `advice_cols * row_count` is a `usize` product (strategy.rs:202-214) and wraps
in a release build: region 0 has two advice columns over `2^63` rows, area `2^64 = 0`, so Rust
slots region 1 (area 1) first at row 0 and region 0 below it at 1, and keys the enable at row 0.
Lean's `usize` area does the same. Under Simple both reject (region 1 starts at `2^63`). -/
namespace LoweringFixtures.PlacementV1AreaWrap
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let _ ← adviceColumn
  let q ← selector
  gate "g" q do
    let x ← advice a
    return #[("g", x)]

def source : CS := (configure.run {}).2

def g : GateSpec := source.gates[0]?.getD ⟨"", ⟨0, true⟩, #[], #[], false, false⟩

def fixture : Export.Replay.Fixture where
  source := source
  k := 4
  ops := [
    .region "wide" [.assignAdvice ⟨0⟩ 0 witness, .assignAdvice ⟨1⟩ (2 ^ 63 - 1) witness],
    .region "gate" [.assignAdvice ⟨0⟩ 0 witness, .enableGate (cleanGate g) 0]]

#guard (Export.layout source fixture.ops fixture.k (Export.v1 source)).regionStarts == [1, 0]

end LoweringFixtures.PlacementV1AreaWrap
