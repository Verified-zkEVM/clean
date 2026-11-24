import LoweringFixtures.Common

/-! `batched_lookup(Some(q), [([x, y], t0), ([x], t1)])`: a second table column with fewer parallel
inputs than the first. Lean's builder rejects it; Rust's `BatchedArgument::new` asserts every column
has the first one's length (logup.rs:303) and panics. -/
namespace LoweringFixtures.LookupRaggedShort
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let t0 ← fixedColumn
  let t1 ← fixedColumn
  let q ← selector false
  batchedLookup "ragged" q do
    let x ← advice a
    let y ← advice a 1
    return #[(#[x, y], t0), (#[x], t1)]

def source : CS := (configure.run {}).2

def fixture : Export.Replay.Fixture where
  source := source
  k := 4
  ops := [.region "r" [.assignAdvice ⟨0⟩ 0 witness]]

#guard source.lookups.isEmpty && source.rejectedLookups.size == 1 && !source.errors.isEmpty

end LoweringFixtures.LookupRaggedShort
