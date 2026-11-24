import LoweringFixtures.ConstantsLastRow.Fixture

/-! Deferred constants past the usable rows: ConstantsLastRow with a third constant at
row 9 of 9 usable rows. Rust's `assign_fixed` fails with `NotEnoughRowsAvailable`; Lean's
`ConstantsPlaced` rejects. -/
namespace LoweringFixtures.ConstantsOverflow
open Halo2 Midnight

def fixture : Export.Replay.Fixture :=
  { ConstantsLastRow.fixture with ops := [.region "r0" (ConstantsLastRow.body 3)] }

end LoweringFixtures.ConstantsOverflow
