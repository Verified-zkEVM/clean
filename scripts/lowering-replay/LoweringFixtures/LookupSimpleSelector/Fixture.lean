import LoweringFixtures.Common

/-! `batched_lookup(Some(q))` on a simple `q`: Rust panics substituting it (circuit.rs:1993) and
`validate` rejects it. -/
namespace LoweringFixtures.LookupSimpleSelector
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let t ← fixedColumn
  let qs ← selector
  batchedLookup "simple selector" qs do
    let x ← advice a
    return #[(#[x], t)]

def source : CS := (configure.run {}).2

def fixture : Export.Replay.Fixture where
  source := source
  k := 4
  ops := [.loadTable ⟨⟨0⟩⟩ [0, 1], .region "r" [.assignAdvice ⟨0⟩ 0 witness]]

#guard !source.validate.isOk

end LoweringFixtures.LookupSimpleSelector
