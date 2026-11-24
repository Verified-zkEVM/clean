import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage94

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def round27Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place round27Plan 407
theorem round27Count : round27Plan.length = 7 := by decide +kernel
def round27Part0Physical : List (DependencyPlan.PlanAssignment F) := (round27Physical.drop 0).take 64
dependency_snapshot_step round27Part0 tree19778 from round26After
theorem round27Part0Ordered : DependencyPlan.ordered place round26After round27Part0Physical = true := by decide +kernel
def round27Part1Physical : List (DependencyPlan.PlanAssignment F) := (round27Physical.drop 64).take 64
dependency_snapshot_step round27Part1 tree19962 from round27Part0After
theorem round27Part1Ordered : DependencyPlan.ordered place round27Part0After round27Part1Physical = true := by decide +kernel
def round27Part2Physical : List (DependencyPlan.PlanAssignment F) := (round27Physical.drop 128).take 64
dependency_snapshot_step round27Part2 tree20131 from round27Part1After
theorem round27Part2Ordered : DependencyPlan.ordered place round27Part1After round27Part2Physical = true := by decide +kernel
theorem round27Split : round27Physical = round27Part0Physical ++ round27Part1Physical ++ round27Part2Physical := by rfl
attribute [local irreducible] round26After round27Part0Physical round27Part0After round27Part1Physical round27Part1After round27Part2Physical round27Part2After
theorem round27PartsAfter_eq : DependencyPlan.advance round26After round27Physical = round27Part2After := by
  rw [round27Split]
  simp only [DependencyPlan.advance_append, round27Part0After_eq, round27Part1After_eq, round27Part2After_eq]
def round27After : DependencySnapshot.State := round27Part2After
theorem round27After_eq : DependencyPlan.advance round26After round27Physical = round27After := round27PartsAfter_eq
theorem round27Ordered : DependencyPlan.ordered place round26After round27Physical = true := by
  rw [round27Split]
  simp only [DependencyPlan.ordered_append, DependencyPlan.advance_append, round27Part0After_eq, round27Part1After_eq, round27Part0Ordered, round27Part1Ordered, round27Part2Ordered, Bool.true_and]

end Midnight.SHA256.WitnessDependencyAcceptance
