import LoweringFixtures.Common

/-! Gate fixed queries at rotations other than zero: rotation -1 at a region's row 0 (row -1
wraps in Rust), +7 past the region and, enabled at the last usable row, past the usable rows, the
same column at 2, 0 and again 2 in one closure, an equality-enabled fixed column queried at -2
before `enable_equality` registers its rotation 0, an unused rotated query, and a second gate
re-querying a rotation another gate registered. -/
namespace LoweringFixtures.FixedRotationEdges
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let f ← fixedColumn
  let g ← fixedColumn
  let q ← selector
  let p ← selector false
  gate "edges" q do
    let x ← advice a
    let up ← fixed f (-1)
    let far ← fixed f 7
    let two ← fixed f 2
    let cur ← fixed f
    let _ ← fixed f 2
    let back ← fixed g (-2)
    let _ ← fixed g 3
    return #[("wrap", Rust.mul up x), ("far", Rust.sub far two), ("mix", Rust.mul (Rust.mul cur back) x)]
  enableEquality ⟨.fixed, g⟩
  gate "again" p do
    let y ← fixed g 3
    let z ← fixed f 7
    return #[("again", Rust.sub y z)]

def source : CS := (configure.run {}).2

def edges : GateSpec := source.gates[0]?.getD ⟨"", ⟨0, true⟩, #[], #[], false, false⟩
def again : GateSpec := source.gates[1]?.getD ⟨"", ⟨0, true⟩, #[], #[], false, false⟩

/-- `k = 4`, 6 blinding rows: usable rows 0..8; "last" starts at 3, so its row 5 is row 8. -/
def fixture : Export.Replay.Fixture where
  source := source
  k := 4
  ops := [
    .region "start" [.assignAdvice ⟨0⟩ 0 witness, .enableGate (cleanGate edges) 0, .assignFixed ⟨0⟩ 0 5],
    .region "fixed" [.assignFixed ⟨1⟩ 0 3, .assignFixed ⟨0⟩ 1 2, .enableGate (cleanGate again) 1],
    .region "last" [.assignAdvice ⟨0⟩ 5 witness, .enableGate (cleanGate edges) 5,
      .enableGate (cleanGate again) 5]]

#guard (Export.layout source fixture.ops fixture.k).regionStarts == [0, 1, 3]

#guard source.fixedQueries == #[(0, -1), (0, 7), (0, 2), (0, 0), (1, -2), (1, 3), (1, 0)]

end LoweringFixtures.FixedRotationEdges
