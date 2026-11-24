import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage37

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def expand34Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place expand34Plan 127
theorem expand34Count : expand34Plan.length = 3 := by decide +kernel
dependency_snapshot_step expand34 tree4814 from expand33After
theorem expand34Ordered : DependencyPlan.ordered place expand33After expand34Physical = true := by decide +kernel

end Midnight.SHA256.WitnessDependencyAcceptance
