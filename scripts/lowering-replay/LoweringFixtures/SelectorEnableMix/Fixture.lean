import LoweringFixtures.Common

/-! Partial and foreign enables Rust keys. Complex `q` carries two gates, a trash argument
and an owned two-tuple lookup; `q2` a `lookup_any` with an advice table; `qs` a simple gate; `qu`
nothing. Row 0 enables one gate, row 1 one tuple, row 2 tuple 0 with `enabled = [q, q2]`, row 3
`q2`'s handle, row 4 `qu` through an unconfigured gate and `qs` twice, row 5 the additive gate's
empty entry. An advice cell only instance copies touch (row 7, copied to two instance rows) and a
copy before its cell's `assignAdvice` set the region height. -/
namespace LoweringFixtures.SelectorEnableMix
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let b ← adviceColumn
  let t ← fixedColumn
  let inst ← instanceColumn
  let q ← selector false
  let q2 ← selector false
  let qs ← selector
  let _qu ← selector false
  enableEquality ⟨.advice, a⟩
  enableEquality ⟨.instance, inst⟩
  enableEquality ⟨.advice, b⟩
  gate "bool" q do
    let x ← advice a
    return #[("bool", Rust.sub (Rust.mul x x) x)]
  gate "next" q do
    let x ← advice a
    let y ← advice a 1
    return #[("next", Rust.sub y x)]
  additiveGate "trash" q do
    let x ← advice b
    return #[("b", x), ("ab", Rust.mul x (← advice a))]
  batchedLookup "owned" q do
    let x ← advice a
    let y ← advice b
    return #[(#[x, y], t)]
  lookupAny "dynamic" q2 do
    let tb ← advice b
    let x ← advice a
    return #[(x, tb)]
  gate "simple" qs do
    let x ← advice b
    return #[("s", Rust.mul x x)]

def source : CS := (configure.run {}).2

def g (i : Nat) : GateSpec := source.gates[i]?.getD ⟨"", ⟨0, true⟩, #[], #[], false, false⟩
def lk (i : Nat) : BatchedLookup := source.lookups[i]?.getD ⟨"", .const 0, #[], #[]⟩

def ops : Operations F := [.loadTable ⟨⟨0⟩⟩ [0, 1, 2],
  .region "r" ([0, 1, 2, 3, 4, 5, 6].map (.assignAdvice ⟨0⟩ · witness) ++
    [.constrainInstance (cell 0 2 .advice 1) ⟨0⟩ 2] ++
    [0, 1, 2, 3, 4, 5].map (.assignAdvice ⟨1⟩ · witness) ++
    [.enableGate (cleanGate (g 1)) 0,
     .enableLookup (cleanLookup (lk 0) 1) [⟨0, false⟩] 1,
     .enableLookup (cleanLookup (lk 0)) [⟨0, false⟩, ⟨1, false⟩] 2,
     .enableGate (lookupHandle (lk 1) 1) 3,
     .enableGate (cleanGate ⟨"u", ⟨3, false⟩, #[], #[], false, false⟩) 4,
     .enableGate (cleanGate (g 3)) 4, .enableGate (cleanGate (g 3)) 4,
     .enableGate (cleanGate (g 2)) 5,
     .constrainInstance (cell 0 7 .advice 0) ⟨0⟩ 0,
     .constrainInstance (cell 0 7 .advice 0) ⟨0⟩ 1]),
  .region "after" [.assignAdvice ⟨0⟩ 0 witness, .constrainEqual (cell 1 0 .advice 0) (cell 0 7 .advice 0)]]

def fixture : Export.Replay.Fixture where
  source := source
  k := 5
  ops := ops

#guard source.validate.isOk && source.unusedSelectors == [3] && (g 2).constraints.isEmpty
#guard (lk 0).owned && !(lk 1).owned && (source.trashcans.map (·.rows)) == #[false]

end LoweringFixtures.SelectorEnableMix
