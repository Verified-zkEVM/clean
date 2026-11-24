import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage90

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def round23Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place round23Plan 379
theorem round23Count : round23Plan.length = 7 := by decide +kernel
def round23Part0Physical : List (DependencyPlan.PlanAssignment F) := (round23Physical.drop 0).take 64
dependency_snapshot_step round23Part0 tree17584 from round22After
theorem round23Part0Ordered : DependencyPlan.ordered place round22After round23Part0Physical = true := by decide +kernel
def round23Part1Physical : List (DependencyPlan.PlanAssignment F) := (round23Physical.drop 64).take 64
dependency_snapshot_step round23Part1 tree17775 from round23Part0After
theorem round23Part1Ordered : DependencyPlan.ordered place round23Part0After round23Part1Physical = true := by decide +kernel
def round23Part2Physical : List (DependencyPlan.PlanAssignment F) := (round23Physical.drop 128).take 64
dependency_snapshot_step round23Part2 tree17949 from round23Part1After
theorem round23Part2Ordered : DependencyPlan.ordered place round23Part1After round23Part2Physical = true := by decide +kernel
theorem round23Split : round23Physical = round23Part0Physical ++ round23Part1Physical ++ round23Part2Physical := by rfl
attribute [local irreducible] round22After round23Part0Physical round23Part0After round23Part1Physical round23Part1After round23Part2Physical round23Part2After
theorem round23PartsAfter_eq : DependencyPlan.advance round22After round23Physical = round23Part2After := by
  rw [round23Split]
  simp only [DependencyPlan.advance_append, round23Part0After_eq, round23Part1After_eq, round23Part2After_eq]
def round23After : DependencySnapshot.State := round23Part2After
theorem round23After_eq : DependencyPlan.advance round22After round23Physical = round23After := round23PartsAfter_eq
theorem round23Ordered : DependencyPlan.ordered place round22After round23Physical = true := by
  rw [round23Split]
  simp only [DependencyPlan.ordered_append, DependencyPlan.advance_append, round23Part0After_eq, round23Part1After_eq, round23Part0Ordered, round23Part1Ordered, round23Part2Ordered, Bool.true_and]

end Midnight.SHA256.WitnessDependencyAcceptance
