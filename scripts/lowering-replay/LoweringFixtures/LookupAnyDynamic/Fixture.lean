import LoweringFixtures.Common

/-! `batched_lookup_any(Some(q))` with selector-free dynamic tables, not owned (Clean's `env` does
not pin advice or instance tables) and enabled through its handle: inputs `x, x(1)` against an advice table at rotation -1 and an instance table, queried
before the inputs; then a bare fixed table queried before a fixed input at rotation 1, which
`batched_lookup` would register after it, owned and enabled per tuple. -/
namespace LoweringFixtures.LookupAnyDynamic
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let b ← adviceColumn
  let f ← fixedColumn
  let t ← fixedColumn
  let inst ← instanceColumn
  let q ← selector false
  batchedLookupAny "dynamic" q do
    let tb ← advice b (-1)
    let ti ← query (.instance ⟨inst⟩ 0)
    let x ← advice a
    let y ← advice a 1
    return #[(#[x, y], tb), (#[y, x], ti)]
  batchedLookupAny "fixed first" q do
    let tt ← fixed t
    let z ← fixed f 1
    return #[(#[z], tt)]

def source : CS := (configure.run {}).2

def lk (i : Nat) : BatchedLookup := source.lookups[i]?.getD ⟨"", .const 0, #[], #[]⟩

def fixture : Export.Replay.Fixture where
  source := source
  k := 5
  ops := [.loadTable ⟨⟨1⟩⟩ [3, 4, 5],
    .region "table" ((List.range 4).map fun r => .assignAdvice ⟨1⟩ r witness),
    .region "use" [.assignAdvice ⟨0⟩ 0 witness, .assignAdvice ⟨0⟩ 1 witness, .assignFixed ⟨0⟩ 1 4,
      .enableGate (lookupHandle (lk 0) 0) 0, .enableLookup (cleanLookup (lk 1) 0) [⟨0, false⟩] 0]]

#guard source.validate.isOk && !(lk 0).owned && (lk 1).owned && (lk 1).stated fixture.ops
#guard source.fixedQueries == #[(1, 0), (0, 1)]

end LoweringFixtures.LookupAnyDynamic
