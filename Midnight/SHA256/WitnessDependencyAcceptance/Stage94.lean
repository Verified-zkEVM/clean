import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage93

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def round26Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place round26Plan 400
theorem round26Count : round26Plan.length = 7 := by decide +kernel
def round26Part0Physical : List (DependencyPlan.PlanAssignment F) := (round26Physical.drop 0).take 64
dependency_snapshot_step round26Part0 tree19253 from round25After
theorem round26Part0Ordered : DependencyPlan.ordered place round25After round26Part0Physical = true := by decide +kernel
def round26Part1Physical : List (DependencyPlan.PlanAssignment F) := (round26Physical.drop 64).take 64
dependency_snapshot_step round26Part1 tree19433 from round26Part0After
theorem round26Part1Ordered : DependencyPlan.ordered place round26Part0After round26Part1Physical = true := by decide +kernel
def round26Part2Physical : List (DependencyPlan.PlanAssignment F) := (round26Physical.drop 128).take 64
dependency_snapshot_step round26Part2 tree19593 from round26Part1After
theorem round26Part2Ordered : DependencyPlan.ordered place round26Part1After round26Part2Physical = true := by decide +kernel
theorem round26Split : round26Physical = round26Part0Physical ++ round26Part1Physical ++ round26Part2Physical := by rfl
attribute [local irreducible] round25After round26Part0Physical round26Part0After round26Part1Physical round26Part1After round26Part2Physical round26Part2After
theorem round26PartsAfter_eq : DependencyPlan.advance round25After round26Physical = round26Part2After := by
  rw [round26Split]
  simp only [DependencyPlan.advance_append, round26Part0After_eq, round26Part1After_eq, round26Part2After_eq]
def round26After : DependencySnapshot.State := round26Part2After
theorem round26After_eq : DependencyPlan.advance round25After round26Physical = round26After := round26PartsAfter_eq
theorem round26Ordered : DependencyPlan.ordered place round25After round26Physical = true := by
  rw [round26Split]
  simp only [DependencyPlan.ordered_append, DependencyPlan.advance_append, round26Part0After_eq, round26Part1After_eq, round26Part0Ordered, round26Part1Ordered, round26Part2Ordered, Bool.true_and]

end Midnight.SHA256.WitnessDependencyAcceptance
