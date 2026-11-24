import LoweringFixtures.Common

/-! `Constraints::with_selector(q1, [q2 * x])` with complex `q2`: Rust pins `q1 * (q2 * x)`, a
`rows` gate, since enabling `q1` alone would read `q2` as zero. -/
namespace LoweringFixtures.SelectorInBody
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let q1 ← selector
  let q2 ← selector false
  gate "inner" q1 do
    let x ← advice a
    return #[("", Rust.mul (querySelector q2) x)]

def source : CS := (configure.run {}).2

def fixture : Export.Replay.Fixture where
  source := source
  k := 4
  ops := [.region "r" [.assignAdvice ⟨0⟩ 0 witness]]

end LoweringFixtures.SelectorInBody
