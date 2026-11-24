import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage121

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def round54Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place round54Plan 596
theorem round54Count : round54Plan.length = 7 := by decide +kernel
def round54Part0Physical : List (DependencyPlan.PlanAssignment F) := (round54Physical.drop 0).take 64
dependency_snapshot_step round54Part0 tree34896 from round53After
theorem round54Part0Ordered : DependencyPlan.ordered place round53After round54Part0Physical = true := by decide +kernel
def round54Part1Physical : List (DependencyPlan.PlanAssignment F) := (round54Physical.drop 64).take 64
dependency_snapshot_step round54Part1 tree35099 from round54Part0After
theorem round54Part1Ordered : DependencyPlan.ordered place round54Part0After round54Part1Physical = true := by decide +kernel
def round54Part2Physical : List (DependencyPlan.PlanAssignment F) := (round54Physical.drop 128).take 64
dependency_snapshot_step round54Part2 tree35283 from round54Part1After
theorem round54Part2Ordered : DependencyPlan.ordered place round54Part1After round54Part2Physical = true := by decide +kernel
theorem round54Split : round54Physical = round54Part0Physical ++ round54Part1Physical ++ round54Part2Physical := by rfl
attribute [local irreducible] round53After round54Part0Physical round54Part0After round54Part1Physical round54Part1After round54Part2Physical round54Part2After
theorem round54PartsAfter_eq : DependencyPlan.advance round53After round54Physical = round54Part2After := by
  rw [round54Split]
  simp only [DependencyPlan.advance_append, round54Part0After_eq, round54Part1After_eq, round54Part2After_eq]
def round54After : DependencySnapshot.State := round54Part2After
theorem round54After_eq : DependencyPlan.advance round53After round54Physical = round54After := round54PartsAfter_eq
theorem round54Ordered : DependencyPlan.ordered place round53After round54Physical = true := by
  rw [round54Split]
  simp only [DependencyPlan.ordered_append, DependencyPlan.advance_append, round54Part0After_eq, round54Part1After_eq, round54Part0Ordered, round54Part1Ordered, round54Part2Ordered, Bool.true_and]

end Midnight.SHA256.WitnessDependencyAcceptance
