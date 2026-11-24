import LoweringFixtures.Common

/-! One complex selector `q` behind three lookup forms: an owned two-tuple `batched_lookup` into
table column `t`, a `lookup_any(Some(q))` that reads `q` itself, `t` at rotation 1 (a table column
queried as a plain fixed column) and `t + qs * 0` (a simple selector folded out of a table), and a
`lookup_any(None)` whose table is `-(q * a)`. `q` is enabled at row 0 by the owned lookup and at
row 2 by the `Some(q)` lookup's handle, each with the owned tuples; equality and a simple-selector
gate are interleaved with the configuration. -/
namespace LoweringFixtures.LookupMixedOwnership
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let c ← adviceColumn
  let t ← fixedColumn
  let f ← fixedColumn
  let q ← selector false
  let qs ← selector
  gate "simple" qs do
    let x ← advice c
    return #[("", Rust.mul x x)]
  batchedLookup "owned" q do
    let x ← advice a
    let y ← advice c 1
    return #[(#[x, y], t)]
  enableEquality ⟨.advice, 1⟩
  lookupAny "shared" q do
    let f2 ← fixed f 2
    let sq ← query (.selector q)
    let t1 ← fixed t 1
    let y ← advice c
    let t0 ← fixed t
    return #[(Rust.sub y (Rust.mul sq f2), t1), (y, .add t0 (Rust.mul (querySelector qs) (.const 0)))]
  lookupAny "none" none do
    let sq ← query (.selector q)
    let x ← advice a (-1)
    let w ← advice a
    return #[(x, Rust.neg (Rust.mul sq w))]

def source : CS := (configure.run {}).2

def lk (i : Nat) : BatchedLookup := source.lookups[i]?.getD ⟨"", .const 0, #[], #[]⟩
def simple : GateSpec := source.gates[0]?.getD ⟨"", ⟨0, true⟩, #[], #[], false, false⟩

def fixture : Export.Replay.Fixture where
  source := source
  k := 5
  ops := [.loadTable ⟨⟨0⟩⟩ [1, 2, 3],
    .region "r" [.assignAdvice ⟨0⟩ 0 witness, .assignAdvice ⟨1⟩ 1 witness,
      .enableLookup (cleanLookup (lk 0) 0) [⟨0, false⟩] 0, .enableLookup (cleanLookup (lk 0) 1) [⟨0, false⟩] 0,
      .enableGate (cleanGate simple) 1, .assignFixed ⟨1⟩ 2 5, .assignAdvice ⟨0⟩ 2 witness,
      .enableGate (lookupHandle (lk 1) 0) 2,
      .enableLookup (cleanLookup (lk 0) 0) [⟨0, false⟩] 2, .enableLookup (cleanLookup (lk 0) 1) [⟨0, false⟩] 2,
      .assignAdvice ⟨1⟩ 3 witness, .constrainEqual (cell 0 1 .advice 1) (cell 0 3 .advice 1)]]

#guard source.validate.isOk && (lk 0).owned && !(lk 1).owned && !(lk 2).owned
#guard (lk 1).handles.map (·.selector.index) == [0, 1] && (lk 2).handles.map (·.selector.index) == [0]
#guard source.fixedQueries == #[(0, 0), (1, 2), (0, 1)]

end LoweringFixtures.LookupMixedOwnership
