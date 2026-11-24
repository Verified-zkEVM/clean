import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage133

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def serialize1Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place serialize1Plan 676
theorem serialize1Count : serialize1Plan.length = 2 := by decide +kernel
dependency_snapshot_step serialize1 tree41552 from serialize0After
theorem serialize1Ordered : DependencyPlan.ordered place serialize0After serialize1Physical = true := by decide +kernel

end Midnight.SHA256.WitnessDependencyAcceptance
