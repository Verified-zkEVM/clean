import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage89

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def round22Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place round22Plan 372
theorem round22Count : round22Plan.length = 7 := by decide +kernel
def round22Part0Physical : List (DependencyPlan.PlanAssignment F) := (round22Physical.drop 0).take 64
dependency_snapshot_step round22Part0 tree17020 from round21After
theorem round22Part0Ordered : DependencyPlan.ordered place round21After round22Part0Physical = true := by decide +kernel
def round22Part1Physical : List (DependencyPlan.PlanAssignment F) := (round22Physical.drop 64).take 64
dependency_snapshot_step round22Part1 tree17216 from round22Part0After
theorem round22Part1Ordered : DependencyPlan.ordered place round22Part0After round22Part1Physical = true := by decide +kernel
def round22Part2Physical : List (DependencyPlan.PlanAssignment F) := (round22Physical.drop 128).take 64
dependency_snapshot_step round22Part2 tree17392 from round22Part1After
theorem round22Part2Ordered : DependencyPlan.ordered place round22Part1After round22Part2Physical = true := by decide +kernel
theorem round22Split : round22Physical = round22Part0Physical ++ round22Part1Physical ++ round22Part2Physical := by rfl
attribute [local irreducible] round21After round22Part0Physical round22Part0After round22Part1Physical round22Part1After round22Part2Physical round22Part2After
theorem round22PartsAfter_eq : DependencyPlan.advance round21After round22Physical = round22Part2After := by
  rw [round22Split]
  simp only [DependencyPlan.advance_append, round22Part0After_eq, round22Part1After_eq, round22Part2After_eq]
def round22After : DependencySnapshot.State := round22Part2After
theorem round22After_eq : DependencyPlan.advance round21After round22Physical = round22After := round22PartsAfter_eq
theorem round22Ordered : DependencyPlan.ordered place round21After round22Physical = true := by
  rw [round22Split]
  simp only [DependencyPlan.ordered_append, DependencyPlan.advance_append, round22Part0After_eq, round22Part1After_eq, round22Part0Ordered, round22Part1Ordered, round22Part2Ordered, Bool.true_and]

end Midnight.SHA256.WitnessDependencyAcceptance
