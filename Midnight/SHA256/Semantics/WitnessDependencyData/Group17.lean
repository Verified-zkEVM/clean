import Midnight.SHA256.Semantics.WitnessDependencyData.Group16
import Midnight.SHA256.Semantics.WitnessCheckpointData
import Midnight.SHA256.Semantics.DependencyPlanSyntax

namespace Midnight.SHA256.Semantics.WitnessCheckpoints
open Halo2 Midnight.Math.Witness

def serialize3Plan : List (List (RegionPlan.RelativeAssignment F)) :=
  dependency_plan% CompactPlan.observe (serialize3Operations 0)

def serialize4Plan : List (List (RegionPlan.RelativeAssignment F)) :=
  dependency_plan% CompactPlan.observe (serialize4Operations 0)

def serialize5Plan : List (List (RegionPlan.RelativeAssignment F)) :=
  dependency_plan% CompactPlan.observe (serialize5Operations 0)

def serialize6Plan : List (List (RegionPlan.RelativeAssignment F)) :=
  dependency_plan% CompactPlan.observe (serialize6Operations 0)

def serialize7Plan : List (List (RegionPlan.RelativeAssignment F)) :=
  dependency_plan% CompactPlan.observe (serialize7Operations 0)

def publicPlan : List (List (RegionPlan.RelativeAssignment F)) :=
  dependency_plan% CompactPlan.observe (publicOperations 0)

end Midnight.SHA256.Semantics.WitnessCheckpoints
