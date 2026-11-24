import LoweringFixtures.V1Constants.Fixture

/-! V1Constants with five more constants: its ten constant positions (f1 rows 2-5, f0 rows 0-5,
all below `first_unassigned_row` = 6) are too few, so Rust's V1 fails with
`NotEnoughColumnsForConstants` (v1.rs:118-120), while Simple puts the eleven on f1 and keys. -/
namespace LoweringFixtures.V1ConstantsShort
open Halo2 Midnight Midnight.Keygen

def source : CS := V1Constants.source

def fixture : Export.Replay.Fixture :=
  { V1Constants.fixture with k := 6, ops := V1Constants.ops [
      .constrainConstant (cell 3 0 .advice 0) 8, .constrainConstant (cell 3 0 .advice 0) 8,
      .constrainConstant (cell 0 0 .advice 0) 5, .constrainConstant (cell 2 0 .advice 0) 7,
      .constrainConstant (cell 3 1 .advice 0) (-1)] }

#guard (Chips.Layout.v1Positions [1, 0] (Chips.Canonical.rustOps source fixture.ops)).length == 10

#guard !(Export.checkLayout source fixture.ops fixture.k (Export.v1 source)).isOk

end LoweringFixtures.V1ConstantsShort
