import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage11

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def prepare8Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place prepare8Plan 65
theorem prepare8Count : prepare8Plan.length = 1 := by decide +kernel
dependency_snapshot_step prepare8 tree881 from prepare7After
theorem prepare8Ordered : DependencyPlan.ordered place prepare7After prepare8Physical = true := by cbv

end Midnight.SHA256.WitnessDependencyAcceptance
