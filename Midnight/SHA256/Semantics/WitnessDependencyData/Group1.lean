import Midnight.SHA256.Semantics.WitnessDependencyData.Group0
import Midnight.SHA256.Semantics.WitnessCheckpointData
import Midnight.SHA256.Semantics.DependencyPlanSyntax

namespace Midnight.SHA256.Semantics.WitnessCheckpoints
open Halo2 Midnight.Math.Witness

def prepare4Plan : List (List (RegionPlan.RelativeAssignment F)) :=
  dependency_plan% CompactPlan.observe (prepare4Operations 0)

def prepare5Plan : List (List (RegionPlan.RelativeAssignment F)) :=
  dependency_plan% CompactPlan.observe (prepare5Operations 0)

def prepare6Plan : List (List (RegionPlan.RelativeAssignment F)) :=
  dependency_plan% CompactPlan.observe (prepare6Operations 0)

def prepare7Plan : List (List (RegionPlan.RelativeAssignment F)) :=
  dependency_plan% CompactPlan.observe (prepare7Operations 0)

def prepare8Plan : List (List (RegionPlan.RelativeAssignment F)) :=
  dependency_plan% CompactPlan.observe (prepare8Operations 0)

def prepare9Plan : List (List (RegionPlan.RelativeAssignment F)) :=
  dependency_plan% CompactPlan.observe (prepare9Operations 0)

def prepare10Plan : List (List (RegionPlan.RelativeAssignment F)) :=
  dependency_plan% CompactPlan.observe (prepare10Operations 0)

def prepare11Plan : List (List (RegionPlan.RelativeAssignment F)) :=
  dependency_plan% CompactPlan.observe (prepare11Operations 0)

end Midnight.SHA256.Semantics.WitnessCheckpoints
