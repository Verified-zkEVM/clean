import LoweringFixtures.Common

/-! Two complex selectors crossing lookups, a rows gate, constants and instance copies:
`lookup_any(Some(q1))` of `q2 * x(-1)` in `q2 * t + f(1)` (a selector in input and table, `t`
written by `assign_fixed`), `batched_lookup(None)` of `q1 * x` in a loaded table, an owned
`Some(q2)` lookup into the same table, and a `without_selector` gate on `q1 * q2 * y` (no single
owner). `q2` is enabled on table rows through the first lookup's handle together with the owned
batch; `q1` only through handles. -/
namespace LoweringFixtures.LookupSelectorCrossUse
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let b ← adviceColumn
  let c ← fixedColumn
  let t ← fixedColumn
  let t2 ← fixedColumn
  let f ← fixedColumn
  let inst ← instanceColumn
  let q1 ← selector false
  let q2 ← selector false
  enableEquality ⟨.instance, inst⟩
  enableEquality ⟨.advice, a⟩
  lookupAny "cross" q1 do
    let s2 ← query (.selector q2)
    let x ← advice a (-1)
    let tv ← fixed t
    let f1 ← fixed f 1
    return #[(Rust.mul s2 x, .add (Rust.mul s2 tv) f1)]
  gateWithoutSelector "rows" do
    let y ← advice b
    return #[("", Rust.mul (Rust.mul (querySelector q1) (querySelector q2)) y)]
  batchedLookup "none sel" none do
    let x ← advice a
    return #[(#[Rust.mul (querySelector q1) x], t2)]
  enableConstant c
  batchedLookup "owned" q2 do
    let y ← advice b 1
    return #[(#[y], t2)]

def source : CS := (configure.run {}).2

def lk (i : Nat) : BatchedLookup := source.lookups[i]?.getD ⟨"", .const 0, #[], #[]⟩

def q2At (row : Nat) : RegionOperations F :=
  [.enableGate (lookupHandle (lk 0) 1) row, .enableLookup (cleanLookup (lk 2)) [⟨1, false⟩] row]

def fixture : Export.Replay.Fixture where
  source := source
  k := 5
  ops := [.loadTable ⟨⟨2⟩⟩ [0, 3, 6],
    .region "tab" ((List.range 4).map (fun r => .assignFixed ⟨1⟩ r (r + 1)) ++ q2At 0 ++ q2At 2 ++
      [.assignFixed ⟨3⟩ 1 5, .assignAdvice ⟨1⟩ 3 witness]),
    .region "use" ([.assignAdvice ⟨0⟩ 0 witness, .assignAdvice ⟨0⟩ 1 witness, .assignAdvice ⟨0⟩ 2 witness,
      .assignAdvice ⟨1⟩ 0 witness, .enableGate (lookupHandle (lk 0) 0) 1] ++ q2At 1 ++
      [.constrainConstant (cell 1 0 .advice 0) 4]),
    .constrainInstance (cell 1 2 .advice 0) ⟨0⟩ 0]

#guard source.validate.isOk && !(lk 0).owned && !(lk 1).owned && (lk 2).owned && (lk 2).stated fixture.ops
#guard (lk 0).handles.map (·.selector.index) == [0, 1] && (lk 1).handles.map (·.selector.index) == [0]
#guard source.gates.map (·.rows) == #[true]

end LoweringFixtures.LookupSelectorCrossUse
