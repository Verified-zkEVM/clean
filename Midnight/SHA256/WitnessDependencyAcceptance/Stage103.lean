import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage102

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def round35Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place round35Plan 463
theorem round35Count : round35Plan.length = 7 := by decide +kernel
def round35Part0Physical : List (DependencyPlan.PlanAssignment F) := (round35Physical.drop 0).take 64
dependency_snapshot_step round35Part0 tree24149 from round34After
theorem round35Part0Ordered : DependencyPlan.ordered place round34After round35Part0Physical = true := by decide +kernel
def round35Part1Physical : List (DependencyPlan.PlanAssignment F) := (round35Physical.drop 64).take 64
dependency_snapshot_step round35Part1 tree24338 from round35Part0After
theorem round35Part1Ordered : DependencyPlan.ordered place round35Part0After round35Part1Physical = true := by decide +kernel
def round35Part2Physical : List (DependencyPlan.PlanAssignment F) := (round35Physical.drop 128).take 64
dependency_snapshot_step round35Part2 tree24514 from round35Part1After
theorem round35Part2Ordered : DependencyPlan.ordered place round35Part1After round35Part2Physical = true := by decide +kernel
theorem round35Split : round35Physical = round35Part0Physical ++ round35Part1Physical ++ round35Part2Physical := by rfl
attribute [local irreducible] round34After round35Part0Physical round35Part0After round35Part1Physical round35Part1After round35Part2Physical round35Part2After
theorem round35PartsAfter_eq : DependencyPlan.advance round34After round35Physical = round35Part2After := by
  rw [round35Split]
  simp only [DependencyPlan.advance_append, round35Part0After_eq, round35Part1After_eq, round35Part2After_eq]
def round35After : DependencySnapshot.State := round35Part2After
theorem round35After_eq : DependencyPlan.advance round34After round35Physical = round35After := round35PartsAfter_eq
theorem round35Ordered : DependencyPlan.ordered place round34After round35Physical = true := by
  rw [round35Split]
  simp only [DependencyPlan.ordered_append, DependencyPlan.advance_append, round35Part0After_eq, round35Part1After_eq, round35Part0Ordered, round35Part1Ordered, round35Part2Ordered, Bool.true_and]

end Midnight.SHA256.WitnessDependencyAcceptance
