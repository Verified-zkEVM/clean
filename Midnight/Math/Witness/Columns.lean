import Midnight.Math.Witness.Operations

/-! Scalar witness execution writes advice and fixed cells only. In particular,
the public statement supplied before execution cannot be changed by the runner. -/
namespace Midnight.Math.Witness.Operations
open Halo2 Execute
variable {F : Type} [FiniteField F]

omit [FiniteField F] in
theorem regionAssignments_not_instance (place : RegionIndex → Nat) (self : RegionIndex)
    (ops : RegionOperations F) (assignment : Assignment F)
    (member : assignment ∈ regionAssignments place self ops) :
    assignment.destination.1.kind ≠ .instance := by
  induction ops with
  | nil => simp [regionAssignments] at member
  | cons op rest ih =>
    cases op <;> simp only [regionAssignments] at member
    all_goals first
      | exact ih member
      | rcases List.mem_cons.mp member with same | tail
        · subst assignment
          intro same
          cases same
        · exact ih tail

omit [FiniteField F] in
theorem assignments_not_instance (place : RegionIndex → Nat) (self : RegionIndex)
    (ops : Operations F) (assignment : Assignment F)
    (member : assignment ∈ assignments place ops self) :
    assignment.destination.1.kind ≠ .instance := by
  induction ops generalizing self with
  | nil => simp [assignments] at member
  | cons op rest ih =>
    cases op with
    | region _ body =>
      rcases List.mem_append.mp member with head | tail
      · exact regionAssignments_not_instance place self body assignment head
      · exact ih (self+1) tail
    | _ => exact ih self member

theorem run_instance (place : RegionIndex → Nat) (self : RegionIndex)
    (ops : Operations F) (initial : ProverEnvironment F) (column : Column .instance) (row : Int) :
    (run place (assignments place ops self) initial).inst column row = initial.inst column row := by
  apply run_preserves_unwritten place (assignments place ops self) initial (column.toAny,row)
  intro assignment member same
  have kind := congrArg (fun location : Address => location.1.kind) same
  exact assignments_not_instance place self ops assignment member kind.symm

end Midnight.Math.Witness.Operations
