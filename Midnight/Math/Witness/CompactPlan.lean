import Midnight.Math.Witness.RegionPlan

/-! Remove repeated cell references within each assignment's dependency plan.
This preserves the exact allowed-read test, including failure for unsupported
programs. Assignment order, duplicate writes and region boundaries are retained. -/
namespace Midnight.Math.Witness.CompactPlan
open Halo2
variable {F V : Type}
attribute [local instance] lexOrd

/-- Assigned cells contain coordinates only; comparing them does not require
decidable equality on their phantom field type. -/
local instance : DecidableEq (AssignedCell F) := by
  intro left right
  cases left with | mk left =>
    cases right with | mk right =>
      exact decidable_of_iff (left = right) (by simp)

def reads [BEq V] : Option (List V) → Option (List V) := Option.map List.eraseDups

theorem accepts_reads [BEq V] [LawfulBEq V] (allowed : V → Bool) (plan : Option (List V)) :
    Dependencies.accepts allowed (reads plan) = Dependencies.accepts allowed plan := by
  cases plan with
  | none => rfl
  | some cells =>
    apply Bool.eq_iff_iff.mpr
    simp only [reads, Option.map_some, Dependencies.accepts, List.all_eq_true, List.mem_eraseDups]

def assignment (plan : DependencyPlan.PlanAssignment F) : DependencyPlan.PlanAssignment F :=
  { plan with reads := reads plan.reads }

theorem ordered_map (place : RegionIndex → Nat) (known : Std.TreeSet (Nat × Nat × Int))
    (plans : List (DependencyPlan.PlanAssignment F)) :
    DependencyPlan.ordered place known (plans.map assignment) = DependencyPlan.ordered place known plans := by
  induction plans generalizing known with
  | nil => rfl
  | cons plan rest ih =>
    simp only [List.map_cons, DependencyPlan.ordered, assignment, accepts_reads, ih]

def relative (plan : RegionPlan.RelativeAssignment F) : RegionPlan.RelativeAssignment F :=
  { plan with reads := reads plan.reads }

def regions (plans : List (List (RegionPlan.RelativeAssignment F))) :
    List (List (RegionPlan.RelativeAssignment F)) := plans.map (List.map relative)

def observe (ops : Halo2.Operations F) : List (List (RegionPlan.RelativeAssignment F)) :=
  regions (RegionPlan.observe ops)

theorem regions_append (left right : List (List (RegionPlan.RelativeAssignment F))) :
    regions (left ++ right) = regions left ++ regions right := List.map_append

theorem observe_append (left right : Halo2.Operations F) :
    observe (left ++ right) = observe left ++ observe right := by
  simp only [observe, RegionPlan.observe_append, regions_append]

theorem lower_regions (place : RegionIndex → Nat) (self : RegionIndex)
    (plans : List (List (RegionPlan.RelativeAssignment F))) :
    RegionPlan.lower place (regions plans) self = (RegionPlan.lower place plans self).map assignment := by
  induction plans generalizing self with
  | nil => rfl
  | cons body rest ih =>
    simp only [regions, List.map_cons, RegionPlan.lower, List.map_append, List.map_map]
    rw [show RegionPlan.lower place (List.map (List.map relative) rest) (self+1) =
      (RegionPlan.lower place rest (self+1)).map assignment from ih (self+1)]
    rfl

/-- A compact source observation certifies the original checker, including its
full witness programs and actual physical-address freshness conditions. -/
theorem check_observe (place : RegionIndex → Nat) (self : RegionIndex)
    (known : Std.TreeSet (Nat × Nat × Int)) (ops : Halo2.Operations F) :
    DependencyPlan.ordered place known (RegionPlan.lower place (observe ops) self) =
      Fast.ordered place known (Operations.assignments place ops self) := by
  rw [observe, lower_regions, ordered_map, RegionPlan.check_observe]

end Midnight.Math.Witness.CompactPlan
