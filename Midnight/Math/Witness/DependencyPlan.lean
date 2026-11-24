import Midnight.Math.Witness.Dependencies
import Midnight.Math.Witness.Fast

/-! Ordered dependency checking using only destination addresses and read plans.
The projection theorem is exact for every source assignment list, including
unsupported programs: a failed extraction remains a rejected assignment.
Chunk composition retains the same set of prior physical addresses. -/
namespace Midnight.Math.Witness.DependencyPlan
open Halo2 Execute
variable {F : Type}
attribute [local instance] lexOrd

structure PlanAssignment (F : Type) where
  destination : Address
  reads : Option (List (AssignedCell F))

/-- Strip witness values and IR syntax only after recording its exact read plan. -/
def project (assignment : Execute.Assignment F) : PlanAssignment F where
  destination := assignment.destination
  reads := Dependencies.program assignment.program

/-- Same physical-address freshness and allowed-read test as `Fast.ordered`. -/
def ordered (place : RegionIndex → Nat) :
    Std.TreeSet (Nat × Nat × Int) → List (PlanAssignment F) → Bool
  | _, [] => true
  | known, assignment :: rest =>
    !known.contains (Fast.key assignment.destination) &&
      Dependencies.accepts (fun cell => known.contains (Fast.key (address place cell))) assignment.reads &&
      ordered place (known.insert (Fast.key assignment.destination)) rest

theorem ordered_project (place : RegionIndex → Nat)
    (known : Std.TreeSet (Nat × Nat × Int)) (assignments : List (Execute.Assignment F)) :
    ordered place known (assignments.map project) = Fast.ordered place known assignments := by
  induction assignments generalizing known with
  | nil => rfl
  | cons assignment rest ih =>
    simp only [List.map_cons, ordered, project, Fast.ordered, Dependencies.program_eq, ih]

/-- The post-state of a chunk. This records destinations even when the chunk
would fail; `ordered_append` ensures a rejected prefix cannot certify a suffix. -/
def advance : Std.TreeSet (Nat × Nat × Int) → List (PlanAssignment F) →
    Std.TreeSet (Nat × Nat × Int)
  | known, [] => known
  | known, assignment :: rest => advance (known.insert (Fast.key assignment.destination)) rest

theorem advance_append (known : Std.TreeSet (Nat × Nat × Int))
    (left right : List (PlanAssignment F)) :
    advance known (left ++ right) = advance (advance known left) right := by
  induction left generalizing known with
  | nil => rfl
  | cons assignment rest ih => exact ih _

theorem ordered_append (place : RegionIndex → Nat)
    (known : Std.TreeSet (Nat × Nat × Int)) (left right : List (PlanAssignment F)) :
    ordered place known (left ++ right) =
      (ordered place known left && ordered place (advance known left) right) := by
  induction left generalizing known with
  | nil => simp only [List.nil_append, ordered, advance, Bool.true_and]
  | cons assignment rest ih =>
    simp only [List.cons_append, ordered, advance, ih, Bool.and_assoc]

end Midnight.Math.Witness.DependencyPlan
