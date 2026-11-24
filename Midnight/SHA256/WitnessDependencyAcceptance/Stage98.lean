import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage97

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def round30Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place round30Plan 428
theorem round30Count : round30Plan.length = 7 := by decide +kernel
def round30Part0Physical : List (DependencyPlan.PlanAssignment F) := (round30Physical.drop 0).take 64
dependency_snapshot_step round30Part0 tree21397 from round29After
theorem round30Part0Ordered : DependencyPlan.ordered place round29After round30Part0Physical = true := by decide +kernel
def round30Part1Physical : List (DependencyPlan.PlanAssignment F) := (round30Physical.drop 64).take 64
dependency_snapshot_step round30Part1 tree21594 from round30Part0After
theorem round30Part1Ordered : DependencyPlan.ordered place round30Part0After round30Part1Physical = true := by decide +kernel
def round30Part2Physical : List (DependencyPlan.PlanAssignment F) := (round30Physical.drop 128).take 64
dependency_snapshot_step round30Part2 tree21768 from round30Part1After
theorem round30Part2Ordered : DependencyPlan.ordered place round30Part1After round30Part2Physical = true := by decide +kernel
theorem round30Split : round30Physical = round30Part0Physical ++ round30Part1Physical ++ round30Part2Physical := by rfl
attribute [local irreducible] round29After round30Part0Physical round30Part0After round30Part1Physical round30Part1After round30Part2Physical round30Part2After
theorem round30PartsAfter_eq : DependencyPlan.advance round29After round30Physical = round30Part2After := by
  rw [round30Split]
  simp only [DependencyPlan.advance_append, round30Part0After_eq, round30Part1After_eq, round30Part2After_eq]
def round30After : DependencySnapshot.State := round30Part2After
theorem round30After_eq : DependencyPlan.advance round29After round30Physical = round30After := round30PartsAfter_eq
theorem round30Ordered : DependencyPlan.ordered place round29After round30Physical = true := by
  rw [round30Split]
  simp only [DependencyPlan.ordered_append, DependencyPlan.advance_append, round30Part0After_eq, round30Part1After_eq, round30Part0Ordered, round30Part1Ordered, round30Part2Ordered, Bool.true_and]

end Midnight.SHA256.WitnessDependencyAcceptance
