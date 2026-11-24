import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage113

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def round46Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place round46Plan 540
theorem round46Count : round46Plan.length = 7 := by decide +kernel
def round46Part0Physical : List (DependencyPlan.PlanAssignment F) := (round46Physical.drop 0).take 64
dependency_snapshot_step round46Part0 tree30352 from round45After
theorem round46Part0Ordered : DependencyPlan.ordered place round45After round46Part0Physical = true := by decide +kernel
def round46Part1Physical : List (DependencyPlan.PlanAssignment F) := (round46Physical.drop 64).take 64
dependency_snapshot_step round46Part1 tree30554 from round46Part0After
theorem round46Part1Ordered : DependencyPlan.ordered place round46Part0After round46Part1Physical = true := by decide +kernel
def round46Part2Physical : List (DependencyPlan.PlanAssignment F) := (round46Physical.drop 128).take 64
dependency_snapshot_step round46Part2 tree30736 from round46Part1After
theorem round46Part2Ordered : DependencyPlan.ordered place round46Part1After round46Part2Physical = true := by decide +kernel
theorem round46Split : round46Physical = round46Part0Physical ++ round46Part1Physical ++ round46Part2Physical := by rfl
attribute [local irreducible] round45After round46Part0Physical round46Part0After round46Part1Physical round46Part1After round46Part2Physical round46Part2After
theorem round46PartsAfter_eq : DependencyPlan.advance round45After round46Physical = round46Part2After := by
  rw [round46Split]
  simp only [DependencyPlan.advance_append, round46Part0After_eq, round46Part1After_eq, round46Part2After_eq]
def round46After : DependencySnapshot.State := round46Part2After
theorem round46After_eq : DependencyPlan.advance round45After round46Physical = round46After := round46PartsAfter_eq
theorem round46Ordered : DependencyPlan.ordered place round45After round46Physical = true := by
  rw [round46Split]
  simp only [DependencyPlan.ordered_append, DependencyPlan.advance_append, round46Part0After_eq, round46Part1After_eq, round46Part0Ordered, round46Part1Ordered, round46Part2Ordered, Bool.true_and]

end Midnight.SHA256.WitnessDependencyAcceptance
