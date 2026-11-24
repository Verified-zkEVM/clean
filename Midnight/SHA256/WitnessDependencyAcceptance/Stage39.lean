import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage38

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def expand35Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place expand35Plan 130
theorem expand35Count : expand35Plan.length = 3 := by decide +kernel
dependency_snapshot_step expand35 tree5005 from expand34After
theorem expand35Ordered : DependencyPlan.ordered place expand34After expand35Physical = true := by decide +kernel

end Midnight.SHA256.WitnessDependencyAcceptance
