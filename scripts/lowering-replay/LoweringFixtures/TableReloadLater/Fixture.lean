import LoweringFixtures.InstanceTableMix.Fixture

/-! `InstanceTableMix` with its first table loaded again after the regions, with other values
and a different length: Rust's layouter fails with `UsedColumn`. -/
namespace LoweringFixtures.TableReloadLater
open Halo2 Midnight

def fixture : Export.Replay.Fixture :=
  { InstanceTableMix.fixture with ops := InstanceTableMix.fixture.ops ++ [.loadTable ⟨⟨0⟩⟩ [7, 8]] }

end LoweringFixtures.TableReloadLater
