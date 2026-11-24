import LoweringFixtures.Common

/-! A `without_selector` sum of two terms on one simple selector: Rust's `+` panics on a simple
selector ("attempted to use a simple selector in an addition"), and `validate` rejects it (`simpleSafe`). -/
namespace LoweringFixtures.RawGateSimpleSum
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let q ← selector
  gateWithoutSelector "sum" do
    let x ← advice a
    let y ← advice a 1
    return #[("", .add (Rust.mul (querySelector q) x) (Rust.mul (querySelector q) y))]

def source : CS := (configure.run {}).2

def fixture : Export.Replay.Fixture where
  source := source
  k := 4
  ops := [.region "r" [.assignAdvice ⟨0⟩ 0 witness, .assignAdvice ⟨0⟩ 1 witness]]

end LoweringFixtures.RawGateSimpleSum
