import LoweringFixtures.Common

/-! A `without_selector` polynomial over two complex selectors, `q1 * x + q2 * y`: Rust enforces
it at every row with both selector columns' values, a `rows` gate. -/
namespace LoweringFixtures.RawGateTwoSelectors
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let q1 ← selector false
  let q2 ← selector false
  gateWithoutSelector "two" do
    let x ← advice a
    let y ← advice a 1
    return #[("", .add (Rust.mul (querySelector q1) x) (Rust.mul (querySelector q2) y))]

def source : CS := (configure.run {}).2

def fixture : Export.Replay.Fixture where
  source := source
  k := 4
  ops := [.region "r" [.assignAdvice ⟨0⟩ 0 witness, .assignAdvice ⟨0⟩ 1 witness]]

end LoweringFixtures.RawGateTwoSelectors
