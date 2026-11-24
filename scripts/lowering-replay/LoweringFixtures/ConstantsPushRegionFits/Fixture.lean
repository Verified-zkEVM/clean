import LoweringFixtures.ConstantsPushRegion.Fixture

/-! `ConstantsPushRegion` with the later region's `assign_fixed` at offset 0, landing on row 8,
the last usable row. -/
namespace LoweringFixtures.ConstantsPushRegionFits
open Midnight

def fixture : Export.Replay.Fixture :=
  { ConstantsPushRegion.fixture with ops := ConstantsPushRegion.ops 0 }

end LoweringFixtures.ConstantsPushRegionFits
