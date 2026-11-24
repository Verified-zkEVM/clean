import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage31

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def expand28Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place expand28Plan 109
theorem expand28Count : expand28Plan.length = 3 := by decide +kernel
dependency_snapshot_step expand28 tree3721 from expand27After
theorem expand28Ordered : DependencyPlan.ordered place expand27After expand28Physical = true := by decide +kernel

end Midnight.SHA256.WitnessDependencyAcceptance
