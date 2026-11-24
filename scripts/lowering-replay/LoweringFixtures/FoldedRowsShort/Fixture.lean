import LoweringFixtures.FoldedRows.Fixture

/-! `FoldedRows` with a second trashcan: 14 blinding factors need 17 rows, one more than
`2^4`, so Rust fails with `NotEnoughRowsAvailable` and Lean's `rows` rejects it. -/
namespace LoweringFixtures.FoldedRowsShort
open Halo2 Midnight Midnight.Keygen

def source : CS :=
  let base := FoldedRows.source
  { base with numSelectors := base.numSelectors + 1, trashcans := base.trashcans.push (FoldedRows.trash 3) }

def fixture : Export.Replay.Fixture where
  source := source
  k := 4
  ops := FoldedRows.ops [FoldedRows.trash 2, FoldedRows.trash 3]

#guard source.blindingFactors + 3 == 17

end LoweringFixtures.FoldedRowsShort
