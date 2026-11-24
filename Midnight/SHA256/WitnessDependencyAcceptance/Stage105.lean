import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage104

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def round37Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place round37Plan 477
theorem round37Count : round37Plan.length = 7 := by decide +kernel
def round37Part0Physical : List (DependencyPlan.PlanAssignment F) := (round37Physical.drop 0).take 64
dependency_snapshot_step round37Part0 tree25275 from round36After
theorem round37Part0Ordered : DependencyPlan.ordered place round36After round37Part0Physical = true := by decide +kernel
def round37Part1Physical : List (DependencyPlan.PlanAssignment F) := (round37Physical.drop 64).take 64
dependency_snapshot_step round37Part1 tree25455 from round37Part0After
theorem round37Part1Ordered : DependencyPlan.ordered place round37Part0After round37Part1Physical = true := by decide +kernel
def round37Part2Physical : List (DependencyPlan.PlanAssignment F) := (round37Physical.drop 128).take 64
dependency_snapshot_step round37Part2 tree25622 from round37Part1After
theorem round37Part2Ordered : DependencyPlan.ordered place round37Part1After round37Part2Physical = true := by decide +kernel
theorem round37Split : round37Physical = round37Part0Physical ++ round37Part1Physical ++ round37Part2Physical := by rfl
attribute [local irreducible] round36After round37Part0Physical round37Part0After round37Part1Physical round37Part1After round37Part2Physical round37Part2After
theorem round37PartsAfter_eq : DependencyPlan.advance round36After round37Physical = round37Part2After := by
  rw [round37Split]
  simp only [DependencyPlan.advance_append, round37Part0After_eq, round37Part1After_eq, round37Part2After_eq]
def round37After : DependencySnapshot.State := round37Part2After
theorem round37After_eq : DependencyPlan.advance round36After round37Physical = round37After := round37PartsAfter_eq
theorem round37Ordered : DependencyPlan.ordered place round36After round37Physical = true := by
  rw [round37Split]
  simp only [DependencyPlan.ordered_append, DependencyPlan.advance_append, round37Part0After_eq, round37Part1After_eq, round37Part0Ordered, round37Part1Ordered, round37Part2Ordered, Bool.true_and]

end Midnight.SHA256.WitnessDependencyAcceptance
