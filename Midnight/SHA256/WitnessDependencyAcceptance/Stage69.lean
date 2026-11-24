import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage68

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def round1Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place round1Plan 225
theorem round1Count : round1Plan.length = 7 := by decide +kernel
dependency_snapshot_step round1 tree11014 from round0After
theorem round1Ordered : DependencyPlan.ordered place round0After round1Physical = true := by decide +kernel

end Midnight.SHA256.WitnessDependencyAcceptance
