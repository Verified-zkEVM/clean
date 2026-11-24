import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage126

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def round59Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place round59Plan 631
theorem round59Count : round59Plan.length = 7 := by decide +kernel
def round59Part0Physical : List (DependencyPlan.PlanAssignment F) := (round59Physical.drop 0).take 64
dependency_snapshot_step round59Part0 tree37782 from round58After
theorem round59Part0Ordered : DependencyPlan.ordered place round58After round59Part0Physical = true := by decide +kernel
def round59Part1Physical : List (DependencyPlan.PlanAssignment F) := (round59Physical.drop 64).take 64
dependency_snapshot_step round59Part1 tree37980 from round59Part0After
theorem round59Part1Ordered : DependencyPlan.ordered place round59Part0After round59Part1Physical = true := by decide +kernel
def round59Part2Physical : List (DependencyPlan.PlanAssignment F) := (round59Physical.drop 128).take 64
dependency_snapshot_step round59Part2 tree38163 from round59Part1After
theorem round59Part2Ordered : DependencyPlan.ordered place round59Part1After round59Part2Physical = true := by decide +kernel
theorem round59Split : round59Physical = round59Part0Physical ++ round59Part1Physical ++ round59Part2Physical := by rfl
attribute [local irreducible] round58After round59Part0Physical round59Part0After round59Part1Physical round59Part1After round59Part2Physical round59Part2After
theorem round59PartsAfter_eq : DependencyPlan.advance round58After round59Physical = round59Part2After := by
  rw [round59Split]
  simp only [DependencyPlan.advance_append, round59Part0After_eq, round59Part1After_eq, round59Part2After_eq]
def round59After : DependencySnapshot.State := round59Part2After
theorem round59After_eq : DependencyPlan.advance round58After round59Physical = round59After := round59PartsAfter_eq
theorem round59Ordered : DependencyPlan.ordered place round58After round59Physical = true := by
  rw [round59Split]
  simp only [DependencyPlan.ordered_append, DependencyPlan.advance_append, round59Part0After_eq, round59Part1After_eq, round59Part0Ordered, round59Part1Ordered, round59Part2Ordered, Bool.true_and]

end Midnight.SHA256.WitnessDependencyAcceptance
