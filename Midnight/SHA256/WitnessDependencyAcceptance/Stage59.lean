import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage58

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def expand55Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place expand55Plan 190
theorem expand55Count : expand55Plan.length = 3 := by decide +kernel
dependency_snapshot_step expand55 tree8835 from expand54After
theorem expand55Ordered : DependencyPlan.ordered place expand54After expand55Physical = true := by decide +kernel

end Midnight.SHA256.WitnessDependencyAcceptance
