import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage114

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def round47Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place round47Plan 547
theorem round47Count : round47Plan.length = 7 := by decide +kernel
def round47Part0Physical : List (DependencyPlan.PlanAssignment F) := (round47Physical.drop 0).take 64
dependency_snapshot_step round47Part0 tree30938 from round46After
theorem round47Part0Ordered : DependencyPlan.ordered place round46After round47Part0Physical = true := by decide +kernel
def round47Part1Physical : List (DependencyPlan.PlanAssignment F) := (round47Physical.drop 64).take 64
dependency_snapshot_step round47Part1 tree31134 from round47Part0After
theorem round47Part1Ordered : DependencyPlan.ordered place round47Part0After round47Part1Physical = true := by decide +kernel
def round47Part2Physical : List (DependencyPlan.PlanAssignment F) := (round47Physical.drop 128).take 64
dependency_snapshot_step round47Part2 tree31315 from round47Part1After
theorem round47Part2Ordered : DependencyPlan.ordered place round47Part1After round47Part2Physical = true := by decide +kernel
theorem round47Split : round47Physical = round47Part0Physical ++ round47Part1Physical ++ round47Part2Physical := by rfl
attribute [local irreducible] round46After round47Part0Physical round47Part0After round47Part1Physical round47Part1After round47Part2Physical round47Part2After
theorem round47PartsAfter_eq : DependencyPlan.advance round46After round47Physical = round47Part2After := by
  rw [round47Split]
  simp only [DependencyPlan.advance_append, round47Part0After_eq, round47Part1After_eq, round47Part2After_eq]
def round47After : DependencySnapshot.State := round47Part2After
theorem round47After_eq : DependencyPlan.advance round46After round47Physical = round47After := round47PartsAfter_eq
theorem round47Ordered : DependencyPlan.ordered place round46After round47Physical = true := by
  rw [round47Split]
  simp only [DependencyPlan.ordered_append, DependencyPlan.advance_append, round47Part0After_eq, round47Part1After_eq, round47Part0Ordered, round47Part1Ordered, round47Part2Ordered, Bool.true_and]

end Midnight.SHA256.WitnessDependencyAcceptance
