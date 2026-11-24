import LoweringFixtures.Common

/-! A `rows` gate `q1 * x + q2 * y` whose second selector `q2` owns no gate: Rust enables `q2`
with `q2.enable(region, 1)`, which is the gate's registered handle on `q2` (`rowsHandles`). -/
namespace LoweringFixtures.RowsSecondSelector
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

def two : GateSpec := source.gates[0]?.getD ⟨"", ⟨0, true⟩, #[], #[], false, false⟩

/-- The same `rows` gate keyed on `q2`: its handle on `q2`. -/
def onSecond : GateSpec := { two with selector := ⟨1, false⟩ }

def fixture : Export.Replay.Fixture where
  source := source
  k := 4
  ops := [.region "r" [.assignAdvice ⟨0⟩ 0 witness, .assignAdvice ⟨0⟩ 1 witness,
    .assignAdvice ⟨0⟩ 2 witness, .enableGate (cleanGate two) 0, .enableGate (cleanGate onSecond) 1]]

#guard source.errors.isEmpty && source.validate.isOk && two.rows && two.selector.index == 0
#guard (if h : two.valid then (two.rowsHandles h).map (·.selector.index) else []) == [1]

end LoweringFixtures.RowsSecondSelector
