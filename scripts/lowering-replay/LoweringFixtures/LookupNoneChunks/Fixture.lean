import LoweringFixtures.Common

/-! A `batched_lookup_any(None)` of five degree-2 tuples (selector `qc` inside two of them, a
constant and a `Rust.sub` element) against an instance table at rotation 1 and a fixed table at
rotation -1. Alone it chunks one tuple per helper, but the owned `qc` lookup lifts the CS degree to
5, so Rust chunks it at the final degree, two per helper: 3 chunks. `qc` is enabled by the owned
lookup and again by the `None` lookup's handle on the same row. -/
namespace LoweringFixtures.LookupNoneChunks
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let b ← adviceColumn
  let t ← fixedColumn
  let f ← fixedColumn
  let inst ← instanceColumn
  let qc ← selector false
  let qs ← selector
  enableEquality ⟨.advice, b⟩
  gate "bool" qs do
    let x ← advice b
    return #[("", Rust.sub (Rust.mul x x) x)]
  batchedLookupAny "none chunks" none do
    let ti ← query (.instance ⟨inst⟩ 1)
    let x ← advice a
    let y ← advice b (-1)
    let sq ← query (.selector qc)
    let tf ← fixed f (-1)
    return #[(#[Rust.mul x y, Rust.mul sq x, Rust.mul y y, Rust.mul x x, Rust.mul sq y], ti),
      (#[x, y, Rust.mul sq (.const 3), .const 7, Rust.sub x y], tf)]
  batchedLookup "owned" qc do
    let x ← advice a 1
    return #[(#[x], t)]

def source : CS := (configure.run {}).2

def lk (i : Nat) : BatchedLookup := source.lookups[i]?.getD ⟨"", .const 0, #[], #[]⟩
def bool : GateSpec := source.gates[0]?.getD ⟨"", ⟨0, true⟩, #[], #[], false, false⟩

def fixture : Export.Replay.Fixture where
  source := source
  k := 5
  ops := [.loadTable ⟨⟨0⟩⟩ [1, 2, 3],
    .region "r1" [.assignAdvice ⟨0⟩ 0 witness, .assignAdvice ⟨0⟩ 1 witness, .assignAdvice ⟨1⟩ 0 witness,
      .enableLookup (cleanLookup (lk 1)) [⟨0, false⟩] 0, .enableGate (cleanGate bool) 1,
      .assignAdvice ⟨1⟩ 1 witness, .assignFixed ⟨1⟩ 2 9],
    .region "r2" [.assignAdvice ⟨1⟩ 0 witness, .enableGate (lookupHandle (lk 0) 0) 0,
      .enableLookup (cleanLookup (lk 1)) [⟨0, false⟩] 0, .assignAdvice ⟨0⟩ 1 witness,
      .constrainEqual (cell 1 0 .advice 1) (cell 0 1 .advice 1)]]

#guard source.validate.isOk && !(lk 0).owned && (lk 1).owned && (lk 1).stated fixture.ops
#guard source.degree == 5 && (lk 0).numChunks source.degree == 3 && (lk 1).numChunks source.degree == 1
#guard (lk 0).handles.map (·.selector.index) == [0]

end LoweringFixtures.LookupNoneChunks
