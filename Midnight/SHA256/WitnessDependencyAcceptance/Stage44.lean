import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage43

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def expand40Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place expand40Plan 145
theorem expand40Count : expand40Plan.length = 3 := by decide +kernel
dependency_snapshot_step expand40 tree5936 from expand39After
theorem expand40Ordered : DependencyPlan.ordered place expand39After expand40Physical = true := by decide +kernel

end Midnight.SHA256.WitnessDependencyAcceptance
