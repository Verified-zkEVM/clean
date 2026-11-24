import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage34

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def expand31Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place expand31Plan 118
theorem expand31Count : expand31Plan.length = 3 := by decide +kernel
dependency_snapshot_step expand31 tree4289 from expand30After
theorem expand31Ordered : DependencyPlan.ordered place expand30After expand31Physical = true := by decide +kernel

end Midnight.SHA256.WitnessDependencyAcceptance
