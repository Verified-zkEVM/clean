import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage25

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def expand22Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place expand22Plan 91
theorem expand22Count : expand22Plan.length = 3 := by decide +kernel
dependency_snapshot_step expand22 tree2687 from expand21After
theorem expand22Ordered : DependencyPlan.ordered place expand21After expand22Physical = true := by decide +kernel

end Midnight.SHA256.WitnessDependencyAcceptance
