import LoweringFixtures.Common

/-! V1's allocation ends wrap (strategy.rs:57, 87): r0 holds `a` over 2^63 + 1 rows, r1 follows at
2^63 + 1 for 2^63 rows, so its enable and constant copy land on row 0, and every column's
`unbounded_interval_start` is 1. `first_unassigned_row` is therefore 1 and the constant goes to
row 0 of the constants column (v1.rs:84-110). Simple places the same way. -/
namespace LoweringFixtures.V1UnboundedWrap
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let c ← fixedColumn
  enableEquality ⟨.advice, a⟩
  enableConstant c
  let q ← selector
  gate "g" q do
    let x ← advice a
    return #[("g", x)]

def source : CS := (configure.run {}).2

def g : GateSpec := source.gates[0]?.getD ⟨"", ⟨0, true⟩, #[], #[], false, false⟩

def fixture : Export.Replay.Fixture where
  source := source
  k := 4
  ops := [
    .region "r0" [.assignAdvice ⟨0⟩ (2 ^ 63) witness],
    .region "r1" [.assignAdvice ⟨0⟩ (2 ^ 63 - 1) witness, .enableGate (cleanGate g) (2 ^ 63 - 1),
      .constrainConstant (cell 1 (2 ^ 63 - 1) .advice 0) 5]]

#guard (Export.layout source fixture.ops fixture.k (Export.v1 source)).regionStarts == [0, 2 ^ 63 + 1]
#guard (Export.layout source fixture.ops fixture.k (Export.v1 source)).copies.length == 1

end LoweringFixtures.V1UnboundedWrap
