import LoweringFixtures.Common

/-! Lookup closures interleaved with a gate and equality enables: the first queries an unused
instance rotation, an unused fixed rotation and a duplicate; the second is two-deep over two
tables with a fixed coefficient and shares the first's complex selector; instance copies. -/
namespace LoweringFixtures.LookupClosureMix
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let b ← adviceColumn
  let f ← fixedColumn
  let t ← fixedColumn
  let t2 ← fixedColumn
  let i ← instanceColumn
  let q ← selector
  let ql ← selector false
  gate "g" q do
    let y ← advice b
    let x ← advice a
    return #[("g", x * y - y)]
  batchedLookup "first" ql do
    let _ ← query (.instance ⟨i⟩ 1)
    let _ ← fixed f (-1)
    let z ← advice a 2
    let _ ← advice b
    let _ ← advice a 2
    return #[(#[z], t)]
  enableEquality ⟨.instance, i⟩
  enableEquality ⟨.advice, a⟩
  batchedLookup "second" ql do
    let w ← advice b (-1)
    let z ← advice a 2
    let c ← fixed f
    return #[(#[w, z], t), (#[c * z, w + c], t2)]

def source : CS := (configure.run {}).2

def g : GateSpec := source.gates[0]?.getD ⟨"", ⟨0, true⟩, #[], #[], false, false⟩
def first : BatchedLookup := source.lookups[0]?.getD ⟨"", .const 0, #[], #[]⟩
def second : BatchedLookup := source.lookups[1]?.getD ⟨"", .const 0, #[], #[]⟩

def lookups (row : Nat) : List (RegionOperation F) :=
  [.enableLookup (cleanLookup first 0) [⟨1, false⟩] row,
   .enableLookup (cleanLookup second 0) [⟨1, false⟩] row,
   .enableLookup (cleanLookup second 1) [⟨1, false⟩] row]

def fixture : Export.Replay.Fixture where
  source := source
  k := 5
  ops := [.loadTable ⟨⟨1⟩⟩ [0, 1, 2],
    .region "use" ([.assignAdvice ⟨0⟩ 0 witness, .assignAdvice ⟨1⟩ 0 witness,
      .assignAdvice ⟨0⟩ 1 witness, .assignAdvice ⟨1⟩ 1 witness,
      .assignAdvice ⟨0⟩ 2 witness, .assignAdvice ⟨0⟩ 3 witness,
      .assignFixed ⟨0⟩ 0 7, .assignFixed ⟨0⟩ 1 2,
      .enableGate (cleanGate g) 1] ++ lookups 1 ++
      [.constrainInstance (cell 0 0 .advice 0) ⟨0⟩ 2]),
    .loadTable ⟨⟨2⟩⟩ [0, 5],
    .region "copy" ([.assignAdvice ⟨0⟩ 0 witness, .assignAdvice ⟨0⟩ 2 witness,
      .assignAdvice ⟨1⟩ 0 witness, .assignFixed ⟨0⟩ 0 1,
      .constrainEqual (cell 1 0 .advice 0) (cell 0 3 .advice 0)] ++ lookups 1),
    .constrainInstance (cell 1 2 .advice 0) ⟨0⟩ 0]

end LoweringFixtures.LookupClosureMix
