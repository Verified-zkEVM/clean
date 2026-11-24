import LoweringFixtures.Common

/-! Regions that only enable lookup selectors (an owned `Some(q1)` batch, and the handle of a
`None` batch reading `q2 * b`), placed by area under V1 (Simple: [0, 0, 4, 7]; V1 sorts the
mixed region first: [3, 3, 0, 3]), with a table loaded between them. -/
namespace LoweringFixtures.LookupV1Shapes
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let b ← adviceColumn
  let t ← fixedColumn
  let q1 ← selector false
  let q2 ← selector false
  batchedLookup "own" q1 do
    let x ← advice a
    return #[(#[x], t)]
  lookupAny "sel" none do
    let s ← query (.selector q2)
    let x ← advice b
    let tt ← fixed t
    return #[(Rust.mul s x, tt)]

def source : CS := (configure.run {}).2

def lk (i : Nat) : BatchedLookup := source.lookups[i]?.getD ⟨"", .const 0, #[], #[]⟩

def fixture : Export.Replay.Fixture where
  source := source
  k := 5
  ops := [.region "only lookup" [.enableLookup (cleanLookup (lk 0)) [⟨0, false⟩] 3],
    .loadTable ⟨⟨0⟩⟩ [0, 5, 7],
    .region "handle only" [.enableGate (lookupHandle (lk 1) 1) 1, .enableGate (lookupHandle (lk 1) 1) 0],
    .region "mixed" [.assignAdvice ⟨0⟩ 0 witness, .assignAdvice ⟨1⟩ 2 witness,
      .enableLookup (cleanLookup (lk 0)) [⟨0, false⟩] 0, .enableGate (lookupHandle (lk 1) 1) 2],
    .region "advice" [.assignAdvice ⟨0⟩ 0 witness, .assignAdvice ⟨0⟩ 1 witness]]

#guard source.validate.isOk && (lk 0).owned && !(lk 1).owned
#guard (Export.layout source fixture.ops fixture.k).regionStarts == [0, 0, 4, 7]
#guard (Export.layout source fixture.ops fixture.k (Export.v1 source)).regionStarts == [3, 3, 0, 3]

end LoweringFixtures.LookupV1Shapes
