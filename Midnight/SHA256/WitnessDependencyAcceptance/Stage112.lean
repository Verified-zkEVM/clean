import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage111

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def round44Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place round44Plan 526
theorem round44Count : round44Plan.length = 7 := by decide +kernel
def round44Part0Physical : List (DependencyPlan.PlanAssignment F) := (round44Physical.drop 0).take 64
dependency_snapshot_step round44Part0 tree29233 from round43After
theorem round44Part0Ordered : DependencyPlan.ordered place round43After round44Part0Physical = true := by decide +kernel
def round44Part1Physical : List (DependencyPlan.PlanAssignment F) := (round44Physical.drop 64).take 64
dependency_snapshot_step round44Part1 tree29428 from round44Part0After
theorem round44Part1Ordered : DependencyPlan.ordered place round44Part0After round44Part1Physical = true := by decide +kernel
def round44Part2Physical : List (DependencyPlan.PlanAssignment F) := (round44Physical.drop 128).take 64
dependency_snapshot_step round44Part2 tree29603 from round44Part1After
theorem round44Part2Ordered : DependencyPlan.ordered place round44Part1After round44Part2Physical = true := by decide +kernel
theorem round44Split : round44Physical = round44Part0Physical ++ round44Part1Physical ++ round44Part2Physical := by rfl
attribute [local irreducible] round43After round44Part0Physical round44Part0After round44Part1Physical round44Part1After round44Part2Physical round44Part2After
theorem round44PartsAfter_eq : DependencyPlan.advance round43After round44Physical = round44Part2After := by
  rw [round44Split]
  simp only [DependencyPlan.advance_append, round44Part0After_eq, round44Part1After_eq, round44Part2After_eq]
def round44After : DependencySnapshot.State := round44Part2After
theorem round44After_eq : DependencyPlan.advance round43After round44Physical = round44After := round44PartsAfter_eq
theorem round44Ordered : DependencyPlan.ordered place round43After round44Physical = true := by
  rw [round44Split]
  simp only [DependencyPlan.ordered_append, DependencyPlan.advance_append, round44Part0After_eq, round44Part1After_eq, round44Part0Ordered, round44Part1Ordered, round44Part2Ordered, Bool.true_and]

end Midnight.SHA256.WitnessDependencyAcceptance
