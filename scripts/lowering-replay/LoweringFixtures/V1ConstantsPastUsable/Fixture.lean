import LoweringFixtures.Common

/-! A V1 constant position past the usable rows. Region 0 writes the constants column f0 at row
0 and advice at row 14, so its rectangle allocates f0 rows 0-14; region 1's advice at row 15
(keygen's `assign_advice` checks nothing) makes `first_unassigned_row` 16, and the one constant
lands on f0 row 15, where keygen's `assign_fixed` fails with `NotEnoughRowsAvailable`. -/
namespace LoweringFixtures.V1ConstantsPastUsable
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let _ ← adviceColumn
  let f0 ← fixedColumn
  enableEquality ⟨.advice, a⟩
  enableConstant f0

def source : CS := (configure.run {}).2

def fixture : Export.Replay.Fixture where
  source := source
  k := 4
  ops := [
    .region "r0" [.assignFixed ⟨0⟩ 0 3, .assignAdvice ⟨0⟩ 0 witness, .assignAdvice ⟨0⟩ 14 witness,
      .constrainConstant (cell 0 0 .advice 0) 4],
    .region "r1" [.assignAdvice ⟨1⟩ 15 witness]]

#guard Chips.Layout.v1Positions [0] (Chips.Canonical.rustOps source fixture.ops) == [(0, 15)]

end LoweringFixtures.V1ConstantsPastUsable
