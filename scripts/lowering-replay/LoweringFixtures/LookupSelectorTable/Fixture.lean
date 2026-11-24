import LoweringFixtures.Common

/-! Selectors in lookup tables: `lookup_any(Some(q1))` of `x` in `q2 * t`, where only rows
enabling `q2` (through a handle) form the table, and of `q1 * x(1)` in `q1 * f`, reading `q1`
at both the input and the table row. `q1` also owns a gate, whose enables activate both lookups. -/
namespace LoweringFixtures.LookupSelectorTable
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let t ← fixedColumn
  let f ← fixedColumn
  let q1 ← selector false
  let q2 ← selector false
  gate "own" q1 do
    let x ← advice a
    return #[("", Rust.sub (Rust.mul x x) x)]
  lookupAny "table selector" q1 do
    let s2 ← query (.selector q2)
    let x ← advice a
    let tv ← fixed t
    return #[(x, Rust.mul s2 tv)]
  lookupAny "self" q1 do
    let s1 ← query (.selector q1)
    let x ← advice a 1
    let fv ← fixed f
    return #[(Rust.mul s1 x, Rust.mul s1 fv)]

def source : CS := (configure.run {}).2

def lk (i : Nat) : BatchedLookup := source.lookups[i]?.getD ⟨"", .const 0, #[], #[]⟩
def own : GateSpec := source.gates[0]?.getD ⟨"", ⟨0, false⟩, #[], #[], false, false⟩

def fixture : Export.Replay.Fixture where
  source := source
  k := 5
  ops := [.region "table" ((List.range 4).flatMap fun r =>
      [.assignFixed ⟨0⟩ r (r + 1), .enableGate (lookupHandle (lk 0) 1) r, .assignFixed ⟨1⟩ r (2 * r)]),
    .region "use" [.assignAdvice ⟨0⟩ 0 witness, .assignAdvice ⟨0⟩ 1 witness, .assignAdvice ⟨0⟩ 2 witness,
      .enableGate (cleanGate own) 0, .enableGate (lookupHandle (lk 1) 0) 1, .enableGate (cleanGate own) 1]]

#guard source.validate.isOk && !(lk 0).owned && !(lk 1).owned
#guard (lk 0).handles.map (·.selector.index) == [0, 1]

end LoweringFixtures.LookupSelectorTable
