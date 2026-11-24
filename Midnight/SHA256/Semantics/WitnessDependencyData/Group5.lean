import Midnight.SHA256.Semantics.WitnessDependencyData.Group4
import Midnight.SHA256.Semantics.WitnessCheckpointData
import Midnight.SHA256.Semantics.DependencyPlanSyntax

namespace Midnight.SHA256.Semantics.WitnessCheckpoints
open Halo2 Midnight.Math.Witness

def expand36Plan : List (List (RegionPlan.RelativeAssignment F)) :=
  dependency_plan% CompactPlan.observe (expand36Operations 0)

def expand37Plan : List (List (RegionPlan.RelativeAssignment F)) :=
  dependency_plan% CompactPlan.observe (expand37Operations 0)

def expand38Plan : List (List (RegionPlan.RelativeAssignment F)) :=
  dependency_plan% CompactPlan.observe (expand38Operations 0)

def expand39Plan : List (List (RegionPlan.RelativeAssignment F)) :=
  dependency_plan% CompactPlan.observe (expand39Operations 0)

def expand40Plan : List (List (RegionPlan.RelativeAssignment F)) :=
  dependency_plan% CompactPlan.observe (expand40Operations 0)

def expand41Plan : List (List (RegionPlan.RelativeAssignment F)) :=
  dependency_plan% CompactPlan.observe (expand41Operations 0)

def expand42Plan : List (List (RegionPlan.RelativeAssignment F)) :=
  dependency_plan% CompactPlan.observe (expand42Operations 0)

def expand43Plan : List (List (RegionPlan.RelativeAssignment F)) :=
  dependency_plan% CompactPlan.observe (expand43Operations 0)

end Midnight.SHA256.Semantics.WitnessCheckpoints
