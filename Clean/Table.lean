import Clean.Utils.Field
import Clean.GenericConstraint
import Mathlib.Tactic
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.ZMod.Basic

section Table
variable (N M : ℕ+) (p : ℕ) [Fact p.Prime]

/--
  A RowConstraint is a constraint that applies to a single row of a table.
  It is a function that takes the row index and returns a GenericConstraint.
-/
def RowConstraint := ZMod M -> GenericConstraint p N M

inductive TableConstraint where
  | boundary : ZMod M -> RowConstraint N M p -> TableConstraint
  | everyRow : RowConstraint N M p -> TableConstraint
  | everyRowExceptLast : RowConstraint N M p -> TableConstraint

structure Table where
  constraints : List (TableConstraint N M p)
  spec : Inputs N M (F p) -> Prop
  equiv :
    ∀ trace : Inputs N M (F p), -- the inputs to the circuit
    (∀ row : ZMod M, forallList constraints (fun c => match c with
      | TableConstraint.boundary constraintRow c
        => forallList (fullLookupSet (c row)) (fun lookup => row = constraintRow -> lookup.prop trace)
      | TableConstraint.everyRow c
        => forallList (fullLookupSet (c row)) ((fun lookup => lookup.prop trace))
      | TableConstraint.everyRowExceptLast c
        => forallList (fullLookupSet (c row)) ((fun lookup => row.val < (M-1) -> lookup.prop trace)))
    ) ->
    (
      (∀ row : ZMod M, forallList constraints (fun c => match c with
        | TableConstraint.boundary constraintRow c
          => forallList (fullConstraintSet (c row)) (fun constraint => row = constraintRow -> constraint.eval trace = 0)
        | TableConstraint.everyRow c
          => forallList (fullConstraintSet (c row)) ((fun constraint => constraint.eval trace = 0))
        | TableConstraint.everyRowExceptLast c
          => forallList (fullConstraintSet (c row)) ((fun constraint => row.val < (M-1) -> constraint.eval trace = 0))))
      ↔
      spec trace
    )


end Table