import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage116

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def round49Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place round49Plan 561
theorem round49Count : round49Plan.length = 7 := by decide +kernel
def round49Part0Physical : List (DependencyPlan.PlanAssignment F) := (round49Physical.drop 0).take 64
dependency_snapshot_step round49Part0 tree32096 from round48After
theorem round49Part0Ordered : DependencyPlan.ordered place round48After round49Part0Physical = true := by decide +kernel
def round49Part1Physical : List (DependencyPlan.PlanAssignment F) := (round49Physical.drop 64).take 64
dependency_snapshot_step round49Part1 tree32296 from round49Part0After
theorem round49Part1Ordered : DependencyPlan.ordered place round49Part0After round49Part1Physical = true := by decide +kernel
def round49Part2Physical : List (DependencyPlan.PlanAssignment F) := (round49Physical.drop 128).take 64
dependency_snapshot_step round49Part2 tree32473 from round49Part1After
theorem round49Part2Ordered : DependencyPlan.ordered place round49Part1After round49Part2Physical = true := by decide +kernel
theorem round49Split : round49Physical = round49Part0Physical ++ round49Part1Physical ++ round49Part2Physical := by rfl
attribute [local irreducible] round48After round49Part0Physical round49Part0After round49Part1Physical round49Part1After round49Part2Physical round49Part2After
theorem round49PartsAfter_eq : DependencyPlan.advance round48After round49Physical = round49Part2After := by
  rw [round49Split]
  simp only [DependencyPlan.advance_append, round49Part0After_eq, round49Part1After_eq, round49Part2After_eq]
def round49After : DependencySnapshot.State := round49Part2After
theorem round49After_eq : DependencyPlan.advance round48After round49Physical = round49After := round49PartsAfter_eq
theorem round49Ordered : DependencyPlan.ordered place round48After round49Physical = true := by
  rw [round49Split]
  simp only [DependencyPlan.ordered_append, DependencyPlan.advance_append, round49Part0After_eq, round49Part1After_eq, round49Part0Ordered, round49Part1Ordered, round49Part2Ordered, Bool.true_and]

end Midnight.SHA256.WitnessDependencyAcceptance
