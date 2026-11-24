import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage132

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def serialize0Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place serialize0Plan 674
theorem serialize0Count : serialize0Plan.length = 2 := by decide +kernel
dependency_snapshot_step serialize0 tree41405 from feedforwardAfter
theorem serialize0Ordered : DependencyPlan.ordered place feedforwardAfter serialize0Physical = true := by decide +kernel

end Midnight.SHA256.WitnessDependencyAcceptance
