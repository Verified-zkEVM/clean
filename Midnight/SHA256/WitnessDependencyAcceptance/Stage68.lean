import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage67

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def round0Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place round0Plan 217
theorem round0Count : round0Plan.length = 8 := by decide +kernel
dependency_snapshot_step round0 tree10723 from expand63After
theorem round0Ordered : DependencyPlan.ordered place expand63After round0Physical = true := by decide +kernel

end Midnight.SHA256.WitnessDependencyAcceptance
