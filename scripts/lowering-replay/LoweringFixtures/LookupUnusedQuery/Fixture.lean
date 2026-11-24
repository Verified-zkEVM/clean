import LoweringFixtures.Common

/-! A lookup closure that queries a cell it does not use (`b` at rotation 1), as a Rust closure
may: `query_advice` registers the query either way. -/
namespace LoweringFixtures.LookupUnusedQuery
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let b ← adviceColumn
  let t ← fixedColumn
  let ql ← selector false
  batchedLookup "unused" ql do
    let x ← advice a
    let _ ← advice b 1
    return #[(#[x], t)]

def source : CS := (configure.run {}).2

def lk : BatchedLookup := source.lookups[0]?.getD ⟨"", .const 0, #[], #[]⟩

def fixture : Export.Replay.Fixture where
  source := source
  k := 4
  ops := [.loadTable ⟨⟨0⟩⟩ [0, 1],
    .region "r" [.assignAdvice ⟨0⟩ 0 witness, .assignAdvice ⟨1⟩ 1 witness,
      .enableLookup (cleanLookup lk) [⟨0, false⟩] 0]]

end LoweringFixtures.LookupUnusedQuery
