import Midnight.SHA256.Semantics.WitnessDependencyData.Group5
import Midnight.SHA256.Semantics.WitnessCheckpointData
import Midnight.SHA256.Semantics.DependencyPlanSyntax

namespace Midnight.SHA256.Semantics.WitnessCheckpoints
open Halo2 Midnight.Math.Witness

def expand44Plan : List (List (RegionPlan.RelativeAssignment F)) :=
  dependency_plan% CompactPlan.observe (expand44Operations 0)

def expand45Plan : List (List (RegionPlan.RelativeAssignment F)) :=
  dependency_plan% CompactPlan.observe (expand45Operations 0)

def expand46Plan : List (List (RegionPlan.RelativeAssignment F)) :=
  dependency_plan% CompactPlan.observe (expand46Operations 0)

def expand47Plan : List (List (RegionPlan.RelativeAssignment F)) :=
  dependency_plan% CompactPlan.observe (expand47Operations 0)

def expand48Plan : List (List (RegionPlan.RelativeAssignment F)) :=
  dependency_plan% CompactPlan.observe (expand48Operations 0)

def expand49Plan : List (List (RegionPlan.RelativeAssignment F)) :=
  dependency_plan% CompactPlan.observe (expand49Operations 0)

def expand50Plan : List (List (RegionPlan.RelativeAssignment F)) :=
  dependency_plan% CompactPlan.observe (expand50Operations 0)

def expand51Plan : List (List (RegionPlan.RelativeAssignment F)) :=
  dependency_plan% CompactPlan.observe (expand51Operations 0)

end Midnight.SHA256.Semantics.WitnessCheckpoints
