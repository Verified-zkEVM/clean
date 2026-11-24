import LoweringFixtures.Common

/-! A simple selector in a `lookup_any` table expression: Rust panics (circuit.rs:1767) and
`validate` rejects it. -/
namespace LoweringFixtures.LookupSimpleTable
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let t ← fixedColumn
  let qs ← selector
  gate "s" qs do
    let x ← advice a
    return #[("", Rust.mul x x)]
  lookupAny "simple table" none do
    let x ← advice a
    let tv ← fixed t
    return #[(x, Rust.mul (querySelector qs) tv)]

def source : CS := (configure.run {}).2

def fixture : Export.Replay.Fixture where
  source := source
  k := 4
  ops := [.region "r" [.assignAdvice ⟨0⟩ 0 witness]]

#guard !source.validate.isOk

end LoweringFixtures.LookupSimpleTable
