import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage117

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def round50Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place round50Plan 568
theorem round50Count : round50Plan.length = 7 := by decide +kernel
def round50Part0Physical : List (DependencyPlan.PlanAssignment F) := (round50Physical.drop 0).take 64
dependency_snapshot_step round50Part0 tree32673 from round49After
theorem round50Part0Ordered : DependencyPlan.ordered place round49After round50Part0Physical = true := by decide +kernel
def round50Part1Physical : List (DependencyPlan.PlanAssignment F) := (round50Physical.drop 64).take 64
dependency_snapshot_step round50Part1 tree32862 from round50Part0After
theorem round50Part1Ordered : DependencyPlan.ordered place round50Part0After round50Part1Physical = true := by decide +kernel
def round50Part2Physical : List (DependencyPlan.PlanAssignment F) := (round50Physical.drop 128).take 64
dependency_snapshot_step round50Part2 tree33030 from round50Part1After
theorem round50Part2Ordered : DependencyPlan.ordered place round50Part1After round50Part2Physical = true := by decide +kernel
theorem round50Split : round50Physical = round50Part0Physical ++ round50Part1Physical ++ round50Part2Physical := by rfl
attribute [local irreducible] round49After round50Part0Physical round50Part0After round50Part1Physical round50Part1After round50Part2Physical round50Part2After
theorem round50PartsAfter_eq : DependencyPlan.advance round49After round50Physical = round50Part2After := by
  rw [round50Split]
  simp only [DependencyPlan.advance_append, round50Part0After_eq, round50Part1After_eq, round50Part2After_eq]
def round50After : DependencySnapshot.State := round50Part2After
theorem round50After_eq : DependencyPlan.advance round49After round50Physical = round50After := round50PartsAfter_eq
theorem round50Ordered : DependencyPlan.ordered place round49After round50Physical = true := by
  rw [round50Split]
  simp only [DependencyPlan.ordered_append, DependencyPlan.advance_append, round50Part0After_eq, round50Part1After_eq, round50Part0Ordered, round50Part1Ordered, round50Part2Ordered, Bool.true_and]

end Midnight.SHA256.WitnessDependencyAcceptance
