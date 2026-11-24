import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage53

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def expand50Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place expand50Plan 175
theorem expand50Count : expand50Plan.length = 3 := by decide +kernel
dependency_snapshot_step expand50 tree7841 from expand49After
theorem expand50Ordered : DependencyPlan.ordered place expand49After expand50Physical = true := by decide +kernel

end Midnight.SHA256.WitnessDependencyAcceptance
