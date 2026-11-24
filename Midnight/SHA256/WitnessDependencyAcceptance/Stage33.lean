import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage32

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def expand29Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place expand29Plan 112
theorem expand29Count : expand29Plan.length = 3 := by decide +kernel
dependency_snapshot_step expand29 tree3908 from expand28After
theorem expand29Ordered : DependencyPlan.ordered place expand28After expand29Physical = true := by decide +kernel

end Midnight.SHA256.WitnessDependencyAcceptance
