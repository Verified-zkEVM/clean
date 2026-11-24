import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage7

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def prepare4Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place prepare4Plan 61
theorem prepare4Count : prepare4Plan.length = 1 := by decide +kernel
dependency_snapshot_step prepare4 tree540 from prepare3After
theorem prepare4Ordered : DependencyPlan.ordered place prepare3After prepare4Physical = true := by cbv

end Midnight.SHA256.WitnessDependencyAcceptance
