import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage119

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def round52Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place round52Plan 582
theorem round52Count : round52Plan.length = 7 := by decide +kernel
def round52Part0Physical : List (DependencyPlan.PlanAssignment F) := (round52Physical.drop 0).take 64
dependency_snapshot_step round52Part0 tree33773 from round51After
theorem round52Part0Ordered : DependencyPlan.ordered place round51After round52Part0Physical = true := by decide +kernel
def round52Part1Physical : List (DependencyPlan.PlanAssignment F) := (round52Physical.drop 64).take 64
dependency_snapshot_step round52Part1 tree33971 from round52Part0After
theorem round52Part1Ordered : DependencyPlan.ordered place round52Part0After round52Part1Physical = true := by decide +kernel
def round52Part2Physical : List (DependencyPlan.PlanAssignment F) := (round52Physical.drop 128).take 64
dependency_snapshot_step round52Part2 tree34147 from round52Part1After
theorem round52Part2Ordered : DependencyPlan.ordered place round52Part1After round52Part2Physical = true := by decide +kernel
theorem round52Split : round52Physical = round52Part0Physical ++ round52Part1Physical ++ round52Part2Physical := by rfl
attribute [local irreducible] round51After round52Part0Physical round52Part0After round52Part1Physical round52Part1After round52Part2Physical round52Part2After
theorem round52PartsAfter_eq : DependencyPlan.advance round51After round52Physical = round52Part2After := by
  rw [round52Split]
  simp only [DependencyPlan.advance_append, round52Part0After_eq, round52Part1After_eq, round52Part2After_eq]
def round52After : DependencySnapshot.State := round52Part2After
theorem round52After_eq : DependencyPlan.advance round51After round52Physical = round52After := round52PartsAfter_eq
theorem round52Ordered : DependencyPlan.ordered place round51After round52Physical = true := by
  rw [round52Split]
  simp only [DependencyPlan.ordered_append, DependencyPlan.advance_append, round52Part0After_eq, round52Part1After_eq, round52Part0Ordered, round52Part1Ordered, round52Part2Ordered, Bool.true_and]

end Midnight.SHA256.WitnessDependencyAcceptance
