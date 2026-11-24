import Midnight.SHA256.Semantics.WitnessDependencyData.Group10
import Midnight.SHA256.Semantics.WitnessCheckpointData
import Midnight.SHA256.Semantics.DependencyPlanSyntax

namespace Midnight.SHA256.Semantics.WitnessCheckpoints
open Halo2 Midnight.Math.Witness

def round20Plan : List (List (RegionPlan.RelativeAssignment F)) :=
  dependency_plan% CompactPlan.observe (round20Operations 0)

def round21Plan : List (List (RegionPlan.RelativeAssignment F)) :=
  dependency_plan% CompactPlan.observe (round21Operations 0)

def round22Plan : List (List (RegionPlan.RelativeAssignment F)) :=
  dependency_plan% CompactPlan.observe (round22Operations 0)

def round23Plan : List (List (RegionPlan.RelativeAssignment F)) :=
  dependency_plan% CompactPlan.observe (round23Operations 0)

def round24Plan : List (List (RegionPlan.RelativeAssignment F)) :=
  dependency_plan% CompactPlan.observe (round24Operations 0)

def round25Plan : List (List (RegionPlan.RelativeAssignment F)) :=
  dependency_plan% CompactPlan.observe (round25Operations 0)

def round26Plan : List (List (RegionPlan.RelativeAssignment F)) :=
  dependency_plan% CompactPlan.observe (round26Operations 0)

def round27Plan : List (List (RegionPlan.RelativeAssignment F)) :=
  dependency_plan% CompactPlan.observe (round27Operations 0)

end Midnight.SHA256.Semantics.WitnessCheckpoints
