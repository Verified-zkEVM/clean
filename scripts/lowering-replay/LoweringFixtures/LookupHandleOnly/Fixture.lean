import LoweringFixtures.Common

/-! One complex `q` behind an owned two-tuple `batched_lookup` and a `lookup_any(Some(q))` into an
advice table, enabled only through the second lookup's handle. Rust's `q.enable` turns on the owned
batch too, which `Canonical.ops` states. -/
namespace LoweringFixtures.LookupHandleOnly
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let b ← adviceColumn
  let t ← fixedColumn
  let q ← selector false
  batchedLookup "owned" q do
    let x ← advice a
    let y ← advice a 1
    return #[(#[x, y], t)]
  lookupAny "dynamic" q do
    let tb ← advice b
    let x ← advice a
    return #[(x, tb)]

def source : CS := (configure.run {}).2

def lk (i : Nat) : BatchedLookup := source.lookups[i]?.getD ⟨"", .const 0, #[], #[]⟩

def fixture : Export.Replay.Fixture where
  source := source
  k := 5
  ops := [.loadTable ⟨⟨0⟩⟩ [0, 1],
    .region "r" [.assignAdvice ⟨0⟩ 0 witness, .assignAdvice ⟨0⟩ 1 witness, .assignAdvice ⟨1⟩ 0 witness,
      .assignAdvice ⟨1⟩ 1 witness, .enableGate (lookupHandle (lk 1) 0) 0]]

#guard source.validate.isOk && (lk 0).owned && !(lk 1).owned

end LoweringFixtures.LookupHandleOnly
