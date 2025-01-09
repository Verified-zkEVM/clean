import Mathlib.Algebra.Field.Basic
import Mathlib.Data.ZMod.Basic
import Clean.Utils.Primes
import Clean.Utils.Vector
import Clean.Circuit.Basic
import Clean.Circuit.Expression
import Clean.Circuit.Provable
import Clean.Utils.Field


def Row (M : ℕ+) (F : Type) := Fin M -> F

/--
  A trace is an inductive list of rows. It can be viewed as a structured
  environment that maps cells to field elements.
-/
inductive Trace (M : ℕ+) (F : Type) :=
  /-- An empty trace -/
  | empty : Trace M F
  /-- Add a row to the end of the trace -/
  | cons (rest: Trace M F) (row: Row M F) : Trace M F

@[inherit_doc] notation:67 "<+>" => Trace.empty
@[inherit_doc] infixl:67 " +> " => Trace.cons

namespace Trace
/--
  The length of a trace is the number of rows it contains.
-/
def len {M : ℕ+} {F : Type} : Trace M F -> ℕ
  | <+> => 0
  | rest +> _ => Nat.succ rest.len

/--
  Induction principle that applies for every row in the trace, where the inductive step takes into
  acount the previous two rows.
-/
def everyRowTwoRowsInduction {M : ℕ+} {F : Type} {P : Trace M F → Sort*}
    (zero : P (<+>))
    (one : ∀ row : Row M F, P (empty +> row))
    (more : ∀ curr next : Row M F,
      ∀ rest : Trace M F, P (rest) -> P (rest +> curr) → P (rest +> curr +> next))
    : ∀ trace, P trace
  | <+> => zero
  | <+> +> first => one first
  | rest +> curr +> _ => more _ _ _
    (everyRowTwoRowsInduction zero one more (rest))
    (everyRowTwoRowsInduction zero one more (rest +> curr))

def getLe {M :ℕ+} {F : Type}:
    (trace : Trace M F) -> (row : Fin trace.len) -> (col : Fin M) -> F
  | _ +> currRow, ⟨0, _⟩, j => currRow j
  | rest +> _, ⟨i + 1, h⟩, j => getLe rest ⟨i, Nat.le_of_succ_le_succ h⟩ j

end Trace

/--
  A trace of length M is a trace with exactly M rows.
-/
def TraceOfLength (M : ℕ+) (N : ℕ) (F : Type) : Type := { env : Trace M F // env.len = N }

namespace TraceOfLength

def get {N: ℕ+} {M : ℕ} {F : Type} : (env : TraceOfLength N M F) -> (i : Fin M) -> (j : Fin N) -> F
  | ⟨env, h⟩, i, j => env.getLe (by rw [←h] at i; exact i) j

end TraceOfLength


section Table
/--
  Apply a proposition to every row in the trace
-/
def forAllRowsOfTrace {N: ℕ+} {M : ℕ} {F : Type} (trace : TraceOfLength N M F) (prop : Row N F -> Prop) : Prop :=
  inner trace.val prop
  where
  inner : Trace N F -> (Row N F -> Prop) -> Prop
    | <+>, _ => true
    | rest +> row, prop => prop row ∧ inner rest prop

/--
  Apply a proposition to every row in the trace except the last one
-/
def forAllRowsOfTraceExceptLast {N: ℕ+} {M : ℕ} {F : Type} (trace : TraceOfLength N M F) (prop : Row N F -> Prop) : Prop :=
  inner trace.val prop
  where
  inner : Trace N F -> (Row N F -> Prop) -> Prop
    | <+>, _ => true
    | <+> +> _, _ => true
    | rest +> curr +> _, prop => prop curr ∧ inner (rest +> curr) prop


/--
  Apply a proposition, which could be dependent on the row index, to every row of the trace
-/
def forAllRowsOfTraceWithIndex {N: ℕ+} {M : ℕ} {F : Type} (trace : TraceOfLength N M F) (prop : Row N F -> ℕ -> Prop) : Prop :=
  inner trace.val prop
  where
  inner : Trace N F -> (Row N F -> ℕ -> Prop) -> Prop
    | <+>, _ => true
    | rest +> row, prop => (prop row rest.len) ∧ inner rest prop

/--
  A cell offset is an offset in a table that points to a specific cell in a row.
  It is used to define a relative position in the trace.
  `W` is the size of the "vertical window", which means that we can reference at most
  `W` rows above the current row.
  To make sure that the vertical offset is bounded, it is represented as a `Fin W`.
-/
structure CellOffset (M W: ℕ+) where
  rowOffset: Fin W
  column: Fin M
deriving Repr

/--
  Mapping from the index of a variable to a cell offset in the table.
-/
@[reducible]
def CellAssignment (M W: ℕ+) := ℕ -> CellOffset M W

inductive TableOperation
    (F : Type) [Field F]
    (M : ℕ+) where
  /--
    A `Boundary` constraint is a constraint that is applied only to a specific row
  -/
  | Boundary (β α : TypePair) [ProvableType F α] [ProvableType F β]:
      FormalCircuit F β α -> CellAssignment M 1 -> (row : ℕ) -> TableOperation F M

  /--
    An `EveryRow` constraint is a constraint that is applied to every row.
    It can only reference cells on the same row
  -/
  | EveryRow (β α : TypePair) [ProvableType F α] [ProvableType F β]:
      FormalCircuit F β α -> CellAssignment M 1 -> TableOperation F M

  /--
    An `EveryRowExceptLast` constraint is a constraint that is applied to every row except the last.
    It can reference cells from the current row, or the next row
  -/
  | EveryRowExceptLast (β α : TypePair) [ProvableType F α] [ProvableType F β]:
      FormalCircuit F β α -> CellAssignment M 2 -> TableOperation F M



/--
  The constraints hold over a trace if the hold individually in a suitable environment, where the
  environment is derived from the `CellAssignment` functions. Intuitively, if a variable `x`
  is assigned to a field element in the trace `y: F` using a `CellAssignment` function, then ` env x = y`
-/
def table_constraints_hold
    (F : Type) [Field F] (M : ℕ+) (N : ℕ)
    (constraints : List (TableOperation F M)) (trace: TraceOfLength M N F) : Prop :=
  foldl constraints trace.val constraints
  where
  /--
  The foldl function applies the constraints to the trace inductively on the trace

  We want to write something like:
  ```
  for row in trace:
    for constraint in constraints:
      apply constraint to row
  ```
  in this exact order, so that the row-inductive structure is at the top-level.

  We do double induction: first on the trace, then on the constraints: we apply every constraint to the current row, and
  then recurse on the rest of the trace.
  `cs` is the list of constraints that we have to apply and it is never changed during the induction
  `cs_iterator` is walked inductively for every row.
  Once the `cs_iterator` is empty, we start again on the rest of the trace with the initial constraints `cs`
  -/
  foldl (cs : List (TableOperation F M)) : Trace M F -> (cs_iterator: List (TableOperation F M)) -> Prop

    -- if the trace has at least two rows and the constraint is a "every row except last" constraint, we apply the constraint
    | trace +> curr +> next, (TableOperation.EveryRowExceptLast β α circuit assignment)::rest =>
        let env : ℕ -> F := fun x =>
          match assignment x with
          | ⟨⟨0, _⟩, j⟩ => curr j
          | ⟨⟨1, _⟩, j⟩ => next j
        let others := foldl cs (trace +> curr +> next) rest
        (∀ b : β.value, ∀ b_var : β.var, Provable.eval_env env b_var = b →
        Circuit.constraints_hold env (circuit.main b_var)) ∧ others

    -- if the trace has at least one row and the constraint is a boundary constraint, we apply the constraint if the
    -- index is the same as the length of the remaining trace
    | trace +> row, (TableOperation.Boundary β α circuit assignment idx)::rest =>
        let env : ℕ -> F := fun x =>
          match assignment x with
          | ⟨⟨0, _⟩, j⟩ => row j
        let others := foldl cs (trace +> row) rest
        if trace.len = idx
        then
          (∀ b : β.value, ∀ b_var : β.var, Provable.eval_env env b_var = b →
          Circuit.constraints_hold env (circuit.main b_var)) ∧ others
        else
          others

    -- if the trace has at least one row and the constraint is a "every row" constraint, we apply the constraint
    | trace +> row, (TableOperation.EveryRow β α circuit assignment)::rest =>
        let env : ℕ -> F := fun x =>
          match assignment x with
          | ⟨⟨0, _⟩, j⟩ => row j
        let others := foldl cs (trace +> row) rest
        (∀ b : β.value, ∀ b_var : β.var, Provable.eval_env env b_var = b →
        Circuit.constraints_hold env (circuit.main b_var)) ∧ others

    -- if the trace has not enough rows for the "every row except last" constraint, we skip the constraint
    -- TODO: this is fine if the trace length M is >= 2, but we should check this somehow
    | trace, (TableOperation.EveryRowExceptLast _ _ _ _)::rest =>
        foldl cs trace rest

    -- if the cs_iterator is empty, we start again with the initial constraints on the next row
    | trace +> _, [] =>
        foldl cs trace cs

    -- if the trace is empty, we are done
    | <+>, _ => True

end Table


section Example
