import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage92

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def round25Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place round25Plan 393
theorem round25Count : round25Plan.length = 7 := by decide +kernel
def round25Part0Physical : List (DependencyPlan.PlanAssignment F) := (round25Physical.drop 0).take 64
dependency_snapshot_step round25Part0 tree18706 from round24After
theorem round25Part0Ordered : DependencyPlan.ordered place round24After round25Part0Physical = true := by decide +kernel
def round25Part1Physical : List (DependencyPlan.PlanAssignment F) := (round25Physical.drop 64).take 64
dependency_snapshot_step round25Part1 tree18899 from round25Part0After
theorem round25Part1Ordered : DependencyPlan.ordered place round25Part0After round25Part1Physical = true := by decide +kernel
def round25Part2Physical : List (DependencyPlan.PlanAssignment F) := (round25Physical.drop 128).take 64
dependency_snapshot_step round25Part2 tree19071 from round25Part1After
theorem round25Part2Ordered : DependencyPlan.ordered place round25Part1After round25Part2Physical = true := by decide +kernel
theorem round25Split : round25Physical = round25Part0Physical ++ round25Part1Physical ++ round25Part2Physical := by rfl
attribute [local irreducible] round24After round25Part0Physical round25Part0After round25Part1Physical round25Part1After round25Part2Physical round25Part2After
theorem round25PartsAfter_eq : DependencyPlan.advance round24After round25Physical = round25Part2After := by
  rw [round25Split]
  simp only [DependencyPlan.advance_append, round25Part0After_eq, round25Part1After_eq, round25Part2After_eq]
def round25After : DependencySnapshot.State := round25Part2After
theorem round25After_eq : DependencyPlan.advance round24After round25Physical = round25After := round25PartsAfter_eq
theorem round25Ordered : DependencyPlan.ordered place round24After round25Physical = true := by
  rw [round25Split]
  simp only [DependencyPlan.ordered_append, DependencyPlan.advance_append, round25Part0After_eq, round25Part1After_eq, round25Part0Ordered, round25Part1Ordered, round25Part2Ordered, Bool.true_and]

end Midnight.SHA256.WitnessDependencyAcceptance
