import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage115

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def round48Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place round48Plan 554
theorem round48Count : round48Plan.length = 7 := by decide +kernel
def round48Part0Physical : List (DependencyPlan.PlanAssignment F) := (round48Physical.drop 0).take 64
dependency_snapshot_step round48Part0 tree31509 from round47After
theorem round48Part0Ordered : DependencyPlan.ordered place round47After round48Part0Physical = true := by decide +kernel
def round48Part1Physical : List (DependencyPlan.PlanAssignment F) := (round48Physical.drop 64).take 64
dependency_snapshot_step round48Part1 tree31707 from round48Part0After
theorem round48Part1Ordered : DependencyPlan.ordered place round48Part0After round48Part1Physical = true := by decide +kernel
def round48Part2Physical : List (DependencyPlan.PlanAssignment F) := (round48Physical.drop 128).take 64
dependency_snapshot_step round48Part2 tree31888 from round48Part1After
theorem round48Part2Ordered : DependencyPlan.ordered place round48Part1After round48Part2Physical = true := by decide +kernel
theorem round48Split : round48Physical = round48Part0Physical ++ round48Part1Physical ++ round48Part2Physical := by rfl
attribute [local irreducible] round47After round48Part0Physical round48Part0After round48Part1Physical round48Part1After round48Part2Physical round48Part2After
theorem round48PartsAfter_eq : DependencyPlan.advance round47After round48Physical = round48Part2After := by
  rw [round48Split]
  simp only [DependencyPlan.advance_append, round48Part0After_eq, round48Part1After_eq, round48Part2After_eq]
def round48After : DependencySnapshot.State := round48Part2After
theorem round48After_eq : DependencyPlan.advance round47After round48Physical = round48After := round48PartsAfter_eq
theorem round48Ordered : DependencyPlan.ordered place round47After round48Physical = true := by
  rw [round48Split]
  simp only [DependencyPlan.ordered_append, DependencyPlan.advance_append, round48Part0After_eq, round48Part1After_eq, round48Part0Ordered, round48Part1Ordered, round48Part2Ordered, Bool.true_and]

end Midnight.SHA256.WitnessDependencyAcceptance
