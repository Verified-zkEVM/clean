import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage44

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def expand41Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place expand41Plan 148
theorem expand41Count : expand41Plan.length = 3 := by decide +kernel
dependency_snapshot_step expand41 tree6122 from expand40After
theorem expand41Ordered : DependencyPlan.ordered place expand40After expand41Physical = true := by decide +kernel

end Midnight.SHA256.WitnessDependencyAcceptance
