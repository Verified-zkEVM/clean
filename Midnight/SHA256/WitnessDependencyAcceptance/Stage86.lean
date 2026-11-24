import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage85

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def round18Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place round18Plan 344
theorem round18Count : round18Plan.length = 7 := by decide +kernel
dependency_snapshot_step round18 tree15941 from round17After
theorem round18Ordered : DependencyPlan.ordered place round17After round18Physical = true := by decide +kernel

end Midnight.SHA256.WitnessDependencyAcceptance
