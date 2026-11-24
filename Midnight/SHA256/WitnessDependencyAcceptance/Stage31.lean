import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage30

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def expand27Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place expand27Plan 106
theorem expand27Count : expand27Plan.length = 3 := by decide +kernel
dependency_snapshot_step expand27 tree3547 from expand26After
theorem expand27Ordered : DependencyPlan.ordered place expand26After expand27Physical = true := by decide +kernel

end Midnight.SHA256.WitnessDependencyAcceptance
