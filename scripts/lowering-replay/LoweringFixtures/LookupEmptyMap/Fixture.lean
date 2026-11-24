import LoweringFixtures.Common

/-! `lookup(Some(q), |_| vec![])`, an empty table map. Rust's `BatchedArgument::new` reads
`input_expressions[0]` and panics (logup.rs:297); Lean's builder rejects it. -/
namespace LoweringFixtures.LookupEmptyMap
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let q ← selector false
  gate "g" q do
    let x ← advice a
    return #[("g", x)]
  batchedLookup "empty" q do return #[]

def source : CS := (configure.run {}).2

def fixture : Export.Replay.Fixture where
  source := source
  k := 4
  ops := [.region "r" [.assignAdvice ⟨0⟩ 0 witness]]

#guard source.lookups.isEmpty && source.rejectedLookups.size == 1 && !source.errors.isEmpty

end LoweringFixtures.LookupEmptyMap
