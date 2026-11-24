import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage109

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def round42Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place round42Plan 512
theorem round42Count : round42Plan.length = 7 := by decide +kernel
def round42Part0Physical : List (DependencyPlan.PlanAssignment F) := (round42Physical.drop 0).take 64
dependency_snapshot_step round42Part0 tree28077 from round41After
theorem round42Part0Ordered : DependencyPlan.ordered place round41After round42Part0Physical = true := by decide +kernel
def round42Part1Physical : List (DependencyPlan.PlanAssignment F) := (round42Physical.drop 64).take 64
dependency_snapshot_step round42Part1 tree28278 from round42Part0After
theorem round42Part1Ordered : DependencyPlan.ordered place round42Part0After round42Part1Physical = true := by decide +kernel
def round42Part2Physical : List (DependencyPlan.PlanAssignment F) := (round42Physical.drop 128).take 64
dependency_snapshot_step round42Part2 tree28458 from round42Part1After
theorem round42Part2Ordered : DependencyPlan.ordered place round42Part1After round42Part2Physical = true := by decide +kernel
theorem round42Split : round42Physical = round42Part0Physical ++ round42Part1Physical ++ round42Part2Physical := by rfl
attribute [local irreducible] round41After round42Part0Physical round42Part0After round42Part1Physical round42Part1After round42Part2Physical round42Part2After
theorem round42PartsAfter_eq : DependencyPlan.advance round41After round42Physical = round42Part2After := by
  rw [round42Split]
  simp only [DependencyPlan.advance_append, round42Part0After_eq, round42Part1After_eq, round42Part2After_eq]
def round42After : DependencySnapshot.State := round42Part2After
theorem round42After_eq : DependencyPlan.advance round41After round42Physical = round42After := round42PartsAfter_eq
theorem round42Ordered : DependencyPlan.ordered place round41After round42Physical = true := by
  rw [round42Split]
  simp only [DependencyPlan.ordered_append, DependencyPlan.advance_append, round42Part0After_eq, round42Part1After_eq, round42Part0Ordered, round42Part1Ordered, round42Part2Ordered, Bool.true_and]

end Midnight.SHA256.WitnessDependencyAcceptance
