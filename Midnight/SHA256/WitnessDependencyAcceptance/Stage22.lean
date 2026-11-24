import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage21

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def expand18Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place expand18Plan 79
theorem expand18Count : expand18Plan.length = 3 := by decide +kernel
dependency_snapshot_step expand18 tree2008 from expand17After
theorem expand18Ordered : DependencyPlan.ordered place expand17After expand18Physical = true := by decide +kernel

end Midnight.SHA256.WitnessDependencyAcceptance
