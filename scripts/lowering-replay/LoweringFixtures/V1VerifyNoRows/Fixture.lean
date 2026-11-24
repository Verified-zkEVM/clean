import LoweringFixtures.Common

/-! Regions that assign nothing and queue constants on their own (unassigned) advice cells, plus a
table. V1 allocates no rows, so `first_unassigned_row` is 0 and there is no constant position
(`NotEnoughColumnsForConstants`); Simple puts them on f rows 0-1. -/
namespace LoweringFixtures.V1VerifyNoRows
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let f ← fixedColumn
  let t ← fixedColumn
  let q ← selector false
  enableEquality ⟨.advice, a⟩
  enableConstant f
  batchedLookup "t" q do
    let x ← advice a
    return #[(#[x], t)]

def source : CS := (configure.run {}).2

def fixture : Export.Replay.Fixture where
  source := source
  k := 4
  ops := [
    .loadTable ⟨⟨1⟩⟩ [0, 1, 2],
    .region "r0" [.constrainConstant (cell 0 0 .advice 0) 3],
    .region "r1" [.constrainConstant (cell 1 1 .advice 0) 4, .constrainEqual (cell 0 0 .advice 0) (cell 1 1 .advice 0)]]

#guard Chips.Layout.v1Positions [0] (Chips.Canonical.rustOps source fixture.ops) == []

end LoweringFixtures.V1VerifyNoRows
