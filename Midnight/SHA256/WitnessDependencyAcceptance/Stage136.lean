import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage135

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def serialize3Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place serialize3Plan 680
theorem serialize3Count : serialize3Plan.length = 2 := by decide +kernel
dependency_snapshot_step serialize3 tree41851 from serialize2After
theorem serialize3Ordered : DependencyPlan.ordered place serialize2After serialize3Physical = true := by decide +kernel

end Midnight.SHA256.WitnessDependencyAcceptance
