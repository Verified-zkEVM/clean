import LoweringFixtures.Common

/-! Simple's column end `region_start + row_count` wraps (single_pass.rs:104): r1 starts at 1 with
2^64 - 1 rows, so column `a` is free again from row 0 and r2 starts there, enabling row 0. Under V1
r1 is placed first and r2 after it at 2^64 - 1, so both reject the enable. -/
namespace LoweringFixtures.ColumnEndWrap
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
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
    .region "r0" [.assignAdvice ⟨0⟩ 0 witness],
    .region "r1" [.assignAdvice ⟨0⟩ (2 ^ 64 - 2) witness],
    .region "r2" [.assignAdvice ⟨0⟩ 0 witness, .enableGate (cleanGate g) 0]]

#guard (Export.layout source fixture.ops fixture.k).regionStarts == [0, 1, 0]
#guard (Export.layout source fixture.ops fixture.k (Export.v1 source)).regionStarts ==
  [2 ^ 64 - 1, 0, 2 ^ 64 - 1]

end LoweringFixtures.ColumnEndWrap
