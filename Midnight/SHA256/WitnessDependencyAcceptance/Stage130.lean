import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage129

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def round62Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place round62Plan 652
theorem round62Count : round62Plan.length = 7 := by decide +kernel
def round62Part0Physical : List (DependencyPlan.PlanAssignment F) := (round62Physical.drop 0).take 64
dependency_snapshot_step round62Part0 tree39529 from round61After
theorem round62Part0Ordered : DependencyPlan.ordered place round61After round62Part0Physical = true := by decide +kernel
def round62Part1Physical : List (DependencyPlan.PlanAssignment F) := (round62Physical.drop 64).take 64
dependency_snapshot_step round62Part1 tree39732 from round62Part0After
theorem round62Part1Ordered : DependencyPlan.ordered place round62Part0After round62Part1Physical = true := by decide +kernel
def round62Part2Physical : List (DependencyPlan.PlanAssignment F) := (round62Physical.drop 128).take 64
dependency_snapshot_step round62Part2 tree39912 from round62Part1After
theorem round62Part2Ordered : DependencyPlan.ordered place round62Part1After round62Part2Physical = true := by decide +kernel
theorem round62Split : round62Physical = round62Part0Physical ++ round62Part1Physical ++ round62Part2Physical := by rfl
attribute [local irreducible] round61After round62Part0Physical round62Part0After round62Part1Physical round62Part1After round62Part2Physical round62Part2After
theorem round62PartsAfter_eq : DependencyPlan.advance round61After round62Physical = round62Part2After := by
  rw [round62Split]
  simp only [DependencyPlan.advance_append, round62Part0After_eq, round62Part1After_eq, round62Part2After_eq]
def round62After : DependencySnapshot.State := round62Part2After
theorem round62After_eq : DependencyPlan.advance round61After round62Physical = round62After := round62PartsAfter_eq
theorem round62Ordered : DependencyPlan.ordered place round61After round62Physical = true := by
  rw [round62Split]
  simp only [DependencyPlan.ordered_append, DependencyPlan.advance_append, round62Part0After_eq, round62Part1After_eq, round62Part0Ordered, round62Part1Ordered, round62Part2Ordered, Bool.true_and]

end Midnight.SHA256.WitnessDependencyAcceptance
