import LoweringFixtures.Common

/-! A `without_selector` gate whose first constraint is selected by `q` and whose second, `x - y`,
has no selector: Rust enforces the second on every row of the domain, a `rows` gate. -/
namespace LoweringFixtures.RawGateUnselectedConstraint
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let q ← selector
  gateWithoutSelector "half" do
    let x ← advice a
    let y ← advice a 1
    return #[("selected", Rust.mul (querySelector q) x), ("unselected", Rust.sub x y)]

def source : CS := (configure.run {}).2

def fixture : Export.Replay.Fixture where
  source := source
  k := 4
  ops := [.region "r" [.assignAdvice ⟨0⟩ 0 witness, .assignAdvice ⟨0⟩ 1 witness]]

end LoweringFixtures.RawGateUnselectedConstraint
