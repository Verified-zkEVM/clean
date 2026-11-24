import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage112

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def round45Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place round45Plan 533
theorem round45Count : round45Plan.length = 7 := by decide +kernel
def round45Part0Physical : List (DependencyPlan.PlanAssignment F) := (round45Physical.drop 0).take 64
dependency_snapshot_step round45Part0 tree29795 from round44After
theorem round45Part0Ordered : DependencyPlan.ordered place round44After round45Part0Physical = true := by decide +kernel
def round45Part1Physical : List (DependencyPlan.PlanAssignment F) := (round45Physical.drop 64).take 64
dependency_snapshot_step round45Part1 tree29983 from round45Part0After
theorem round45Part1Ordered : DependencyPlan.ordered place round45Part0After round45Part1Physical = true := by decide +kernel
def round45Part2Physical : List (DependencyPlan.PlanAssignment F) := (round45Physical.drop 128).take 64
dependency_snapshot_step round45Part2 tree30152 from round45Part1After
theorem round45Part2Ordered : DependencyPlan.ordered place round45Part1After round45Part2Physical = true := by decide +kernel
theorem round45Split : round45Physical = round45Part0Physical ++ round45Part1Physical ++ round45Part2Physical := by rfl
attribute [local irreducible] round44After round45Part0Physical round45Part0After round45Part1Physical round45Part1After round45Part2Physical round45Part2After
theorem round45PartsAfter_eq : DependencyPlan.advance round44After round45Physical = round45Part2After := by
  rw [round45Split]
  simp only [DependencyPlan.advance_append, round45Part0After_eq, round45Part1After_eq, round45Part2After_eq]
def round45After : DependencySnapshot.State := round45Part2After
theorem round45After_eq : DependencyPlan.advance round44After round45Physical = round45After := round45PartsAfter_eq
theorem round45Ordered : DependencyPlan.ordered place round44After round45Physical = true := by
  rw [round45Split]
  simp only [DependencyPlan.ordered_append, DependencyPlan.advance_append, round45Part0After_eq, round45Part1After_eq, round45Part0Ordered, round45Part1Ordered, round45Part2Ordered, Bool.true_and]

end Midnight.SHA256.WitnessDependencyAcceptance
