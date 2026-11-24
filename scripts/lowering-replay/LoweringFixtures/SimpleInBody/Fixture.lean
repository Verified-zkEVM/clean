import LoweringFixtures.Common

/-! `with_selector(q1, [q2 * x])` with both selectors simple: Rust's `q1 * poly` panics, and
`validate` rejects it (`simpleSafe`). -/
namespace LoweringFixtures.SimpleInBody
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let q1 ← selector
  let q2 ← selector
  gate "inner" q1 do
    let x ← advice a
    return #[("", Rust.mul (querySelector q2) x)]

def source : CS := (configure.run {}).2

def fixture : Export.Replay.Fixture where
  source := source
  k := 4
  ops := [.region "r" [.assignAdvice ⟨0⟩ 0 witness]]

end LoweringFixtures.SimpleInBody
