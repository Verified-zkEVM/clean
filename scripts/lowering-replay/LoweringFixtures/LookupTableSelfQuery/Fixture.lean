import LoweringFixtures.Common

/-! A lookup whose input queries its own table column at rotation 1 before Rust queries the
table, over the table column twice, then a gate on the same complex selector querying the
advice cells in another order and the table column at `rotation` (0 here, 1 in
`GateFixedRotation`). -/
namespace LoweringFixtures.LookupTableSelfQuery
open Halo2 Midnight Midnight.Keygen

def configure (rotation : Int) : ConfigM Unit := do
  let a ← adviceColumn
  let t ← fixedColumn
  let ql ← selector false
  batchedLookup "self" ql do
    let n ← fixed t 1
    let x ← advice a 1
    let y ← advice a
    return #[(#[x], t), (#[n + y], t)]
  gate "after" ql do
    let y ← advice a
    let x ← advice a 1
    let n ← fixed t rotation
    return #[("after", x - y - n)]

def fixtureAt (rotation : Int) : Export.Replay.Fixture :=
  let source : CS := ((configure rotation).run {}).2
  let after : GateSpec := source.gates[0]?.getD ⟨"", ⟨0, false⟩, #[], #[], false, false⟩
  let self_ : BatchedLookup := source.lookups[0]?.getD ⟨"", .const 0, #[], #[]⟩
  { source, k := 4,
    ops := [.loadTable ⟨⟨0⟩⟩ [3, 4, 5],
      .region "r" [.assignAdvice ⟨0⟩ 0 witness, .assignAdvice ⟨0⟩ 1 witness, .assignAdvice ⟨0⟩ 2 witness,
        .enableGate (cleanGate after) 0, .enableLookup (cleanLookup self_) [⟨0, false⟩] 0,
        .enableLookup (cleanLookup self_) [⟨0, false⟩] 1, .enableGate (cleanGate after) 1]] }

def fixture : Export.Replay.Fixture := fixtureAt 0

end LoweringFixtures.LookupTableSelfQuery
