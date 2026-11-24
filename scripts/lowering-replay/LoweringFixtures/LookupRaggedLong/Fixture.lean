import LoweringFixtures.Common

/-! `batched_lookup_any(None, [([x], a), ([x, y], a·b)])` beside a good lookup: a later column with
more parallel inputs than the first. Rust's `BatchedArgument::new` panics (logup.rs:303). -/
namespace LoweringFixtures.LookupRaggedLong
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let b ← adviceColumn
  let t ← fixedColumn
  let q ← selector false
  batchedLookup "good" q do
    let x ← advice a
    return #[(#[x], t)]
  batchedLookupAny "ragged" none do
    let x ← advice a
    let y ← advice b (-1)
    return #[(#[x], x), (#[x, y], Rust.mul x y)]

def source : CS := (configure.run {}).2

def fixture : Export.Replay.Fixture where
  source := source
  k := 4
  ops := [.region "r" [.assignAdvice ⟨0⟩ 0 witness]]

#guard source.lookups.size == 1 && source.rejectedLookups.size == 1 && !source.errors.isEmpty

end LoweringFixtures.LookupRaggedLong
