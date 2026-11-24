import LoweringFixtures.Common

/-! V1's sort key on shapes only Rust's region calls fix: region 1's advice comes from in-region
instance copies alone (`assign_advice_from_instance`, two columns, area 8), region 0 is sparse (rows
0 and 5, area 6, tied with region 2), region 6's height is set by an instance copy at row 6 (area 7,
tied with region 3), and region 4 enables a lookup's and a simple gate's selectors in one
`enabled` list. Ties go to the later region. -/
namespace LoweringFixtures.V1VerifyInstanceArea
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a0 ← adviceColumn
  let a1 ← adviceColumn
  let a2 ← adviceColumn
  let t ← fixedColumn
  let inst ← instanceColumn
  let ql ← selector false
  let qg ← selector
  enableEquality ⟨.advice, a0⟩
  enableEquality ⟨.advice, a1⟩
  enableEquality ⟨.advice, a2⟩
  enableEquality ⟨.instance, inst⟩
  batchedLookup "l" ql do
    let x ← advice a0
    return #[(#[x], t)]
  gate "g" qg do
    let x ← advice a1
    return #[("g", Rust.mul x x)]

def source : CS := (configure.run {}).2

def g : GateSpec := source.gates[0]?.getD ⟨"", ⟨0, true⟩, #[], #[], false, false⟩
def lk : BatchedLookup := source.lookups[0]?.getD ⟨"", .const 0, #[], #[]⟩

def advice (column rows : Nat) : RegionOperations F :=
  (List.range rows).map fun row => .assignAdvice ⟨column⟩ row witness

def fixture : Export.Replay.Fixture where
  source := source
  k := 5
  ops := [
    .loadTable ⟨⟨0⟩⟩ [0, 1],
    .region "sparse" [.assignAdvice ⟨0⟩ 0 witness, .assignAdvice ⟨0⟩ 5 witness],
    .region "inst" [.constrainInstance (cell 1 0 .advice 1) ⟨0⟩ 0, .constrainInstance (cell 1 1 .advice 1) ⟨0⟩ 1,
      .constrainInstance (cell 1 2 .advice 2) ⟨0⟩ 2, .constrainInstance (cell 1 3 .advice 2) ⟨0⟩ 3],
    .region "pair" (advice 0 3 ++ advice 1 3),
    .region "tall" (advice 2 7 ++ [.constrainEqual (cell 3 6 .advice 2) (cell 1 3 .advice 2)]),
    .region "multi" [.assignAdvice ⟨0⟩ 0 witness, .assignAdvice ⟨1⟩ 1 witness,
      .enableLookup (cleanLookup lk) [⟨0, false⟩, ⟨1, true⟩] 1],
    .region "gate" [.assignAdvice ⟨1⟩ 0 witness, .enableGate (cleanGate g) 0],
    .region "late" [.assignAdvice ⟨0⟩ 0 witness, .constrainInstance (cell 6 6 .advice 0) ⟨0⟩ 4,
      .constrainEqual (cell 6 6 .advice 0) (cell 0 5 .advice 0)],
    .constrainInstance (cell 6 0 .advice 0) ⟨0⟩ 5]

#guard (Export.layout source fixture.ops fixture.k (Export.v1 source)).regionStarts !=
  (Export.layout source fixture.ops fixture.k).regionStarts

end LoweringFixtures.V1VerifyInstanceArea
