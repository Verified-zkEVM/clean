import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage26

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def expand23Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place expand23Plan 94
theorem expand23Count : expand23Plan.length = 3 := by decide +kernel
dependency_snapshot_step expand23 tree2863 from expand22After
theorem expand23Ordered : DependencyPlan.ordered place expand22After expand23Physical = true := by decide +kernel

end Midnight.SHA256.WitnessDependencyAcceptance
