import LoweringFixtures.Common

/-! A simple selector in a lookup input: Rust asserts against it (circuit.rs:1760) and
`validate` rejects it. -/
namespace LoweringFixtures.LookupSimpleInput
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let t ← fixedColumn
  let qs ← selector
  let ql ← selector false
  gate "s" qs do
    let x ← advice a
    return #[("", Rust.mul x x)]
  batchedLookup "simple" ql do
    let x ← advice a
    return #[(#[Rust.mul (querySelector qs) x], t)]

def source : CS := (configure.run {}).2

def fixture : Export.Replay.Fixture where
  source := source
  k := 4
  ops := [.loadTable ⟨⟨0⟩⟩ [0, 1], .region "r" [.assignAdvice ⟨0⟩ 0 witness]]

#guard !source.validate.isOk

end LoweringFixtures.LookupSimpleInput
