import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage137

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def serialize5Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place serialize5Plan 684
theorem serialize5Count : serialize5Plan.length = 2 := by decide +kernel
dependency_snapshot_step serialize5 tree42166 from serialize4After
theorem serialize5Ordered : DependencyPlan.ordered place serialize4After serialize5Physical = true := by decide +kernel

end Midnight.SHA256.WitnessDependencyAcceptance
