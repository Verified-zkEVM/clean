import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage84

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def round17Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place round17Plan 337
theorem round17Count : round17Plan.length = 7 := by decide +kernel
dependency_snapshot_step round17 tree15642 from round16After
theorem round17Ordered : DependencyPlan.ordered place round16After round17Physical = true := by decide +kernel

end Midnight.SHA256.WitnessDependencyAcceptance
