import LoweringFixtures.InstanceCopyOrder.Fixture

/-! `InstanceCopyOrder` with the first region's instance copy before the region assigns that
cell. `assign_advice_from_instance` assigns the cell itself, so Rust keys it with the same
bytes, and so does Lean, whose region assigns the cell later. -/
namespace LoweringFixtures.InstanceCopyFirst
open Halo2 Midnight

def fixture : Export.Replay.Fixture := { InstanceCopyOrder.fixture with ops := InstanceCopyOrder.ops true }

end LoweringFixtures.InstanceCopyFirst
