import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage88

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def round21Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place round21Plan 365
theorem round21Count : round21Plan.length = 7 := by decide +kernel
dependency_snapshot_step round21 tree16819 from round20After

end Midnight.SHA256.WitnessDependencyAcceptance
