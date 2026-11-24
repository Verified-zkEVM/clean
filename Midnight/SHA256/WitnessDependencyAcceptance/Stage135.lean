import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage134

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def serialize2Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place serialize2Plan 678
theorem serialize2Count : serialize2Plan.length = 2 := by decide +kernel
dependency_snapshot_step serialize2 tree41698 from serialize1After
theorem serialize2Ordered : DependencyPlan.ordered place serialize1After serialize2Physical = true := by decide +kernel

end Midnight.SHA256.WitnessDependencyAcceptance
