import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage10

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def prepare7Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place prepare7Plan 64
theorem prepare7Count : prepare7Plan.length = 1 := by decide +kernel
dependency_snapshot_step prepare7 tree801 from prepare6After
theorem prepare7Ordered : DependencyPlan.ordered place prepare6After prepare7Physical = true := by cbv

end Midnight.SHA256.WitnessDependencyAcceptance
