import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage9

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def prepare6Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place prepare6Plan 63
theorem prepare6Count : prepare6Plan.length = 1 := by decide +kernel
dependency_snapshot_step prepare6 tree707 from prepare5After
theorem prepare6Ordered : DependencyPlan.ordered place prepare5After prepare6Physical = true := by cbv

end Midnight.SHA256.WitnessDependencyAcceptance
