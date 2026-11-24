import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage106

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def round39Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place round39Plan 491
theorem round39Count : round39Plan.length = 7 := by decide +kernel
def round39Part0Physical : List (DependencyPlan.PlanAssignment F) := (round39Physical.drop 0).take 64
dependency_snapshot_step round39Part0 tree26377 from round38After
theorem round39Part0Ordered : DependencyPlan.ordered place round38After round39Part0Physical = true := by decide +kernel
def round39Part1Physical : List (DependencyPlan.PlanAssignment F) := (round39Physical.drop 64).take 64
dependency_snapshot_step round39Part1 tree26570 from round39Part0After
theorem round39Part1Ordered : DependencyPlan.ordered place round39Part0After round39Part1Physical = true := by decide +kernel
def round39Part2Physical : List (DependencyPlan.PlanAssignment F) := (round39Physical.drop 128).take 64
dependency_snapshot_step round39Part2 tree26744 from round39Part1After
theorem round39Part2Ordered : DependencyPlan.ordered place round39Part1After round39Part2Physical = true := by decide +kernel
theorem round39Split : round39Physical = round39Part0Physical ++ round39Part1Physical ++ round39Part2Physical := by rfl
attribute [local irreducible] round38After round39Part0Physical round39Part0After round39Part1Physical round39Part1After round39Part2Physical round39Part2After
theorem round39PartsAfter_eq : DependencyPlan.advance round38After round39Physical = round39Part2After := by
  rw [round39Split]
  simp only [DependencyPlan.advance_append, round39Part0After_eq, round39Part1After_eq, round39Part2After_eq]
def round39After : DependencySnapshot.State := round39Part2After
theorem round39After_eq : DependencyPlan.advance round38After round39Physical = round39After := round39PartsAfter_eq
theorem round39Ordered : DependencyPlan.ordered place round38After round39Physical = true := by
  rw [round39Split]
  simp only [DependencyPlan.ordered_append, DependencyPlan.advance_append, round39Part0After_eq, round39Part1After_eq, round39Part0Ordered, round39Part1Ordered, round39Part2Ordered, Bool.true_and]

end Midnight.SHA256.WitnessDependencyAcceptance
