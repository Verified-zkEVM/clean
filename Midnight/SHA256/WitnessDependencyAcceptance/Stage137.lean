import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage136

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def serialize4Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place serialize4Plan 682
theorem serialize4Count : serialize4Plan.length = 2 := by decide +kernel
dependency_snapshot_step serialize4 tree42005 from serialize3After
theorem serialize4Ordered : DependencyPlan.ordered place serialize3After serialize4Physical = true := by decide +kernel

end Midnight.SHA256.WitnessDependencyAcceptance
