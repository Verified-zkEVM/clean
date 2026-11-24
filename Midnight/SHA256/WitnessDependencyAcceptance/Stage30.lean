import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage29

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def expand26Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place expand26Plan 103
theorem expand26Count : expand26Plan.length = 3 := by decide +kernel
dependency_snapshot_step expand26 tree3365 from expand25After
theorem expand26Ordered : DependencyPlan.ordered place expand25After expand26Physical = true := by decide +kernel

end Midnight.SHA256.WitnessDependencyAcceptance
