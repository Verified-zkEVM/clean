import LoweringFixtures.Common

/-! Placement, copies and lookups mixed: regions sharing only a selector column, disjoint
columns, an empty region, a negative-rotation gate, a degree-6 gate with an instance query
at rotation 1 over five equality columns (two permutation chunks), a two-wide, two-deep
lookup with expression inputs enabled twice at one row, tables of different lengths loaded
before and between regions, self and cycle-closing copies, a fixed copy, an in-region
instance copy after an equality, and two layouter instance copies to one instance row. -/
namespace LoweringFixtures.LayoutMix
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let b ← adviceColumn
  let c ← adviceColumn
  let f ← fixedColumn
  let t0 ← fixedColumn
  let t1 ← fixedColumn
  let inst ← instanceColumn
  let q1 ← selector
  let q2 ← selector
  let ql ← selector false
  enableEquality ⟨.instance, inst⟩
  enableEquality ⟨.advice, c⟩
  gate "rot" q1 do
    let prev ← advice a (-1)
    let x ← advice a
    let y ← advice b 1
    return #[("rot", x * y - prev), ("lin", x + y)]
  enableEquality ⟨.advice, a⟩
  enableEquality ⟨.fixed, f⟩
  gate "deg6" q2 do
    let x ← advice a
    let y ← advice b
    let z ← advice c
    let k ← fixed f
    let i ← query (.instance ⟨inst⟩ 1)
    return #[("deg", x * x * y * y * z - k), ("inst", z - i)]
  enableEquality ⟨.advice, b⟩
  batchedLookup "mix" ql do
    let x ← advice a 1
    let y ← advice c
    let k ← fixed f
    return #[(#[x + y, y], t0), (#[k * y, x], t1)]

def source : CS := (configure.run {}).2

def rot : GateSpec := source.gates[0]?.getD ⟨"", ⟨0, true⟩, #[], #[], false, false⟩
def deg6 : GateSpec := source.gates[1]?.getD ⟨"", ⟨0, true⟩, #[], #[], false, false⟩
def mix : BatchedLookup := source.lookups[0]?.getD ⟨"", .const 0, #[], #[]⟩

def ops : Operations F := [
  .loadTable ⟨⟨1⟩⟩ [0, 1, 2, 3, 4],
  .region "a-only" [.assignAdvice ⟨0⟩ 0 witness, .assignAdvice ⟨0⟩ 1 witness,
    .assignAdvice ⟨0⟩ 2 witness, .enableGate (cleanGate rot) 1],
  .region "b-only" [.assignAdvice ⟨1⟩ 4 witness],
  .region "sel-only" [.enableGate (cleanGate rot) 0],
  .region "empty" [],
  .region "ab" [.assignAdvice ⟨0⟩ 0 witness, .assignAdvice ⟨1⟩ 0 witness,
    .constrainEqual (cell 4 0 .advice 0) (cell 0 2 .advice 0),
    .constrainEqual (cell 0 0 .advice 0) (cell 1 4 .advice 1),
    .constrainEqual (cell 4 0 .advice 0) (cell 4 0 .advice 0),
    .constrainEqual (cell 4 0 .advice 1) (cell 0 0 .advice 0),
    .constrainEqual (cell 0 2 .advice 0) (cell 1 4 .advice 1)],
  .loadTable ⟨⟨2⟩⟩ [7, 8],
  .region "fixed" [.assignFixed ⟨0⟩ 0 7, .assignFixed ⟨0⟩ 2 0, .assignAdvice ⟨2⟩ 0 witness,
    .constrainEqual (cell 5 0 .fixed 0) (cell 5 0 .advice 2),
    .constrainInstance (cell 5 0 .advice 2) ⟨0⟩ 3],
  .constrainInstance (cell 0 0 .advice 0) ⟨0⟩ 0,
  .region "deg" [.assignAdvice ⟨0⟩ 0 witness, .assignAdvice ⟨1⟩ 0 witness, .assignAdvice ⟨2⟩ 0 witness,
    .assignAdvice ⟨0⟩ 1 witness, .assignAdvice ⟨1⟩ 1 witness, .assignAdvice ⟨2⟩ 1 witness,
    .assignFixed ⟨0⟩ 1 3, .enableGate (cleanGate deg6) 0, .enableGate (cleanGate deg6) 1,
    .enableLookup (cleanLookup mix 0) [⟨2, false⟩] 1, .enableLookup (cleanLookup mix 1) [⟨2, false⟩] 1,
    .constrainEqual (cell 6 1 .advice 2) (cell 5 0 .fixed 0)],
  .constrainInstance (cell 4 0 .advice 1) ⟨0⟩ 0,
  .region "late-b" [.assignAdvice ⟨1⟩ 0 witness, .constrainEqual (cell 7 0 .advice 1) (cell 6 0 .advice 1)]]

def fixture : Export.Replay.Fixture := { source, ops, k := 6 }

end LoweringFixtures.LayoutMix
