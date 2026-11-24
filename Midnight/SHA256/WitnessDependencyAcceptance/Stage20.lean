import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage19

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def expand16Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place expand16Plan 73
theorem expand16Count : expand16Plan.length = 3 := by decide +kernel
dependency_snapshot_step expand16 tree1699 from prepare15After
theorem expand16Ordered : DependencyPlan.ordered place prepare15After expand16Physical = true := by decide +kernel

end Midnight.SHA256.WitnessDependencyAcceptance
