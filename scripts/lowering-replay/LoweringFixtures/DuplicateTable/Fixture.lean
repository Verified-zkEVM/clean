import LoweringFixtures.Ops.Fixture

/-! `Ops` with its table column loaded a second time, with the same values. Rust's layouter
fails with `UsedColumn`, and Lean rejects it. -/
namespace LoweringFixtures.DuplicateTable
open Halo2 Midnight

def fixture : Export.Replay.Fixture :=
  { Ops.fixture with ops := Ops.ops ++ [.loadTable ⟨⟨1⟩⟩ [0, 1, 2, 3]] }

end LoweringFixtures.DuplicateTable
