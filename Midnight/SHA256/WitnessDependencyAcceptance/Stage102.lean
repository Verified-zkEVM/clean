import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage101

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def round34Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place round34Plan 456
theorem round34Count : round34Plan.length = 7 := by decide +kernel
def round34Part0Physical : List (DependencyPlan.PlanAssignment F) := (round34Physical.drop 0).take 64
dependency_snapshot_step round34Part0 tree23595 from round33After
theorem round34Part0Ordered : DependencyPlan.ordered place round33After round34Part0Physical = true := by decide +kernel
def round34Part1Physical : List (DependencyPlan.PlanAssignment F) := (round34Physical.drop 64).take 64
dependency_snapshot_step round34Part1 tree23787 from round34Part0After
theorem round34Part1Ordered : DependencyPlan.ordered place round34Part0After round34Part1Physical = true := by decide +kernel
def round34Part2Physical : List (DependencyPlan.PlanAssignment F) := (round34Physical.drop 128).take 64
dependency_snapshot_step round34Part2 tree23957 from round34Part1After
theorem round34Part2Ordered : DependencyPlan.ordered place round34Part1After round34Part2Physical = true := by decide +kernel
theorem round34Split : round34Physical = round34Part0Physical ++ round34Part1Physical ++ round34Part2Physical := by rfl
attribute [local irreducible] round33After round34Part0Physical round34Part0After round34Part1Physical round34Part1After round34Part2Physical round34Part2After
theorem round34PartsAfter_eq : DependencyPlan.advance round33After round34Physical = round34Part2After := by
  rw [round34Split]
  simp only [DependencyPlan.advance_append, round34Part0After_eq, round34Part1After_eq, round34Part2After_eq]
def round34After : DependencySnapshot.State := round34Part2After
theorem round34After_eq : DependencyPlan.advance round33After round34Physical = round34After := round34PartsAfter_eq
theorem round34Ordered : DependencyPlan.ordered place round33After round34Physical = true := by
  rw [round34Split]
  simp only [DependencyPlan.ordered_append, DependencyPlan.advance_append, round34Part0After_eq, round34Part1After_eq, round34Part0Ordered, round34Part1Ordered, round34Part2Ordered, Bool.true_and]

end Midnight.SHA256.WitnessDependencyAcceptance
