import Midnight.Math.Witness.DependencyPlan
import Midnight.Math.Witness.Operations

/-! An append-preserving observation of the actual source operations for bounded
dependency certificates. Writes retain region-relative rows; reads retain their
original assigned-cell coordinates. Empty regions are retained because they
consume a region index. Fixed values, gate polynomials and table contents are
irrelevant to this observation, but remain in the source circuit semantics. -/
namespace Midnight.Math.Witness.RegionPlan
open Halo2
variable {F : Type}
attribute [local instance] lexOrd

structure RelativeAssignment (F : Type) where
  column : AnyColumn
  row : Nat
  reads : Option (List (AssignedCell F))

def region : RegionOperations F → List (RelativeAssignment F)
  | [] => []
  | .assignAdvice column row program :: rest =>
    ⟨column, row, Dependencies.program program⟩ :: region rest
  | .assignFixed column row _ :: rest =>
    ⟨column, row, some []⟩ :: region rest
  | _ :: rest => region rest

/-- All region boundaries are retained, including regions with no writes. -/
def observe : Halo2.Operations F → List (List (RelativeAssignment F))
  | [] => []
  | .region _ body :: rest => region body :: observe rest
  | _ :: rest => observe rest

theorem region_append (left right : RegionOperations F) :
    region (left ++ right) = region left ++ region right := by
  induction left with
  | nil => rfl
  | cons op rest ih => cases op <;> simp only [List.cons_append, region, ih, List.cons_append]

theorem observe_append (left right : Halo2.Operations F) :
    observe (left ++ right) = observe left ++ observe right := by
  induction left with
  | nil => rfl
  | cons op rest ih => cases op <;> simp only [List.cons_append, observe, ih, List.cons_append]

def lowerAssignment (place : RegionIndex → Nat) (self : RegionIndex)
    (assignment : RelativeAssignment F) : DependencyPlan.PlanAssignment F :=
  ⟨(assignment.column, (place self + assignment.row : Nat)), assignment.reads⟩

def lower (place : RegionIndex → Nat) :
    List (List (RelativeAssignment F)) → RegionIndex → List (DependencyPlan.PlanAssignment F)
  | [], _ => []
  | body :: rest, self => body.map (lowerAssignment place self) ++ lower place rest (self + 1)

theorem lower_append (place : RegionIndex → Nat)
    (left right : List (List (RelativeAssignment F))) (self : RegionIndex) :
    lower place (left ++ right) self =
      lower place left self ++ lower place right (self + left.length) := by
  induction left generalizing self with
  | nil => simp only [List.nil_append, lower, List.length_nil, Nat.add_zero]
  | cons body rest ih =>
    simp only [List.cons_append, lower, ih, List.length_cons, List.append_assoc,
      Nat.add_right_comm self 1 rest.length, Nat.add_assoc]

theorem region_lower (place : RegionIndex → Nat) (self : RegionIndex)
    (ops : RegionOperations F) :
    (region ops).map (lowerAssignment place self) =
      (Operations.regionAssignments place self ops).map DependencyPlan.project := by
  induction ops with
  | nil => rfl
  | cons op rest ih =>
    cases op <;> simp only [region, Operations.regionAssignments, List.map_cons,
      lowerAssignment, DependencyPlan.project, ih]
    rfl

/-- The observed trace lowers to exactly the plans extracted from every actual
scalar assignment. No source witness expression is replaced or assumed. -/
theorem lower_observe (place : RegionIndex → Nat) (self : RegionIndex)
    (ops : Halo2.Operations F) :
    lower place (observe ops) self =
      (Operations.assignments place ops self).map DependencyPlan.project := by
  induction ops generalizing self with
  | nil => rfl
  | cons op rest ih =>
    cases op <;> simp only [observe, lower, Operations.assignments, List.map_append,
      region_lower, ih]

theorem check_observe (place : RegionIndex → Nat) (self : RegionIndex)
    (known : Std.TreeSet (Nat × Nat × Int)) (ops : Halo2.Operations F) :
    DependencyPlan.ordered place known (lower place (observe ops) self) =
      Fast.ordered place known (Operations.assignments place ops self) := by
  rw [lower_observe, DependencyPlan.ordered_project]

end Midnight.Math.Witness.RegionPlan
