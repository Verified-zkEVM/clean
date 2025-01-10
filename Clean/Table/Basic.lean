import Mathlib.Algebra.Field.Basic
import Mathlib.Data.ZMod.Basic
import Clean.Utils.Primes
import Clean.Utils.Vector
import Clean.Circuit.Basic
import Clean.Circuit.Expression
import Clean.Circuit.Provable
import Clean.Utils.Field

import Clean.GadgetsNew.Add8.Addition8


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

inductive TableConstraint
    (F : Type) [Field F]
    (M : ℕ+) where
  /--
    A `Boundary` constraint is a constraint that is applied only to a specific row
  -/
  | Boundary (β α : TypePair) [ProvableType F α] [ProvableType F β]:
      FormalCircuit F β α -> CellAssignment M 1 -> (row : ℕ) -> TableConstraint F M

  /--
    An `EveryRow` constraint is a constraint that is applied to every row.
    It can only reference cells on the same row
  -/
  | EveryRow {β α : TypePair} [ProvableType F α] [ProvableType F β]:
      FormalCircuit F β α -> CellAssignment M 1 -> TableConstraint F M

  /--
    An `EveryRowExceptLast` constraint is a constraint that is applied to every row except the last.
    It can reference cells from the current row, or the next row
  -/
  | EveryRowExceptLast (β α : TypePair) [ProvableType F α] [ProvableType F β]:
      FormalCircuit F β α -> CellAssignment M 2 -> TableConstraint F M



/--
  The constraints hold over a trace if the hold individually in a suitable environment, where the
  environment is derived from the `CellAssignment` functions. Intuitively, if a variable `x`
  is assigned to a field element in the trace `y: F` using a `CellAssignment` function, then ` env x = y`
-/
def table_constraints_hold
    (F : Type) [Field F] (M : ℕ+) (N : ℕ)
    (constraints : List (TableConstraint F M)) (trace: TraceOfLength M N F) : Prop :=
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
  foldl (cs : List (TableConstraint F M)) : Trace M F -> (cs_iterator: List (TableConstraint F M)) -> Prop

    -- if the trace has at least two rows and the constraint is a "every row except last" constraint, we apply the constraint
    | trace +> curr +> next, (TableConstraint.EveryRowExceptLast β α circuit assignment)::rest =>
        let env : ℕ -> F := fun x =>
          match assignment x with
          | ⟨⟨0, _⟩, j⟩ => curr j
          | ⟨⟨1, _⟩, j⟩ => next j
        let others := foldl cs (trace +> curr +> next) rest
        (∀ b : β.value, ∀ b_var : β.var, Provable.eval_env env b_var = b →
        Circuit.constraints_hold env (circuit.main b_var)) ∧ others

    -- if the trace has at least one row and the constraint is a boundary constraint, we apply the constraint if the
    -- index is the same as the length of the remaining trace
    | trace +> row, (TableConstraint.Boundary β α circuit assignment idx)::rest =>
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
    | trace +> row, (TableConstraint.EveryRow (β :=β) (α:=α) circuit assignment)::rest =>
        let env : ℕ -> F := fun x =>
          match assignment x with
          | ⟨⟨0, _⟩, j⟩ => row j
        let others := foldl cs (trace +> row) rest
        (∀ b : β.value, ∀ b_var : β.var, Provable.eval_env env b_var = b →
        Circuit.constraints_hold env (circuit.main b_var)) ∧ others

    -- if the trace has not enough rows for the "every row except last" constraint, we skip the constraint
    -- TODO: this is fine if the trace length M is >= 2, but we should check this somehow
    | trace, (TableConstraint.EveryRowExceptLast _ _ _ _)::rest =>
        foldl cs trace rest

    -- if the cs_iterator is empty, we start again with the initial constraints on the next row
    | trace +> _, [] =>
        foldl cs trace cs

    -- if the trace is empty, we are done
    | <+>, _ => True


inductive TableOperation (F : Type) [Field F] (M W : ℕ+) where
  /--
    Add some witnessed variable to the context
    TODO: there should be the possibility to work with ProvableType directly in-trace
  -/
  | Witness : CellOffset M W -> (compute : Unit → F) -> TableOperation F M W

  /--
    Allocate a subcircuit in the trace
  -/
  | Allocate: SubCircuit F -> TableOperation F M W

  /--
    Assign a variable to a cell in the trace
  -/
  | Assign : Variable F -> CellOffset M W -> TableOperation F M W

structure TableContext (F : Type) (M W : ℕ+) where
  subContext: Context F
  assignment : CellAssignment M W

@[simp]
def TableContext.empty {F : Type} {M W : ℕ+} : TableContext F M W := ⟨
  Context.empty,
  -- TODO: is there a better way?
  fun _ => ⟨0, 0⟩
⟩

namespace TableOperation

@[simp]
def update_context {F : Type} {M W : ℕ+} [Field F] (ctx: TableContext F M W) : TableOperation F M W → TableContext F M W
  | Witness offset _ => {
      subContext := ⟨ ctx.subContext.offset + 1 ⟩,
      assignment := fun x => if x = ctx.subContext.offset then offset else ctx.assignment x
    }
  | Allocate { ops, .. } => {
      subContext := ⟨ ctx.subContext.offset + PreOperation.witness_length ops ⟩,
      assignment := ctx.assignment
    }
  | Assign v offset => {
      subContext := ctx.subContext,
      assignment := fun x => if x = v.index then offset else ctx.assignment x
    }

instance {F : Type} {M W : ℕ+} [Field F] [Repr F] : ToString (TableOperation F M W) where
  toString
    | Witness offset _ => "(Witness " ++ reprStr offset ++ ")"
    | Allocate {ops, ..} => "(Allocate " ++ reprStr ops ++ ")"
    | Assign v offset => "(Assign " ++ reprStr v ++ " " ++ reprStr offset ++ ")"

@[simp]
def Table (F : Type) [Field F] (M W : ℕ+) (α : Type) :=
  TableContext F M W → (TableContext F M W × List (TableOperation F M W)) × α

namespace Table
instance (F : Type) [Field F] (M W : ℕ+): Monad (Table F M W) where
  pure a ctx := ((ctx, []), a)
  bind f g ctx :=
    let ((ctx', ops), a) := f ctx
    let ((ctx'', ops'), b) := g a ctx'
    ((ctx'', ops ++ ops'), b)


def as_table_operation {α: Type} {F : Type} {M W : ℕ+} [Field F]
  (f : TableContext F M W -> TableOperation F M W × α) : Table F M W α :=
  fun ctx =>
  let (op, a) := f ctx
  let ctx' := update_context ctx op
  ((ctx', [op]), a)

def operations {α : Type} {F : Type} {M W : ℕ+} [Field F] (table : Table F M W α) : List (TableOperation F M W) :=
  let ((_, ops), _) := table TableContext.empty
  ops

def output {α : Type} {F : Type} {M W : ℕ+} [Field F] (table : Table F M W α) : α :=
  let ((_, _), a) := table TableContext.empty
  a


@[simp]
def witness_cell {F : Type} {M W : ℕ+} [Field F] (off : CellOffset M W) (compute : Unit → F): Table F M W (Variable F) :=
  as_table_operation fun ctx =>
  (TableOperation.Witness off compute, ⟨ ctx.subContext.offset, compute ⟩)

@[simp]
def subcircuit
    {F : Type} {M W : ℕ+} [Field F]
    {α β : TypePair} [ProvableType F β] [ProvableType F α]
    (circuit: FormalCircuit F β α) (b: β.var) : Table F M W α.var :=
  as_table_operation fun ctx =>
  let ⟨ a, subcircuit ⟩ := Circuit.formal_circuit_to_subcircuit ctx.subContext circuit b
  (TableOperation.Allocate subcircuit, a)

def assign {F : Type} {M W : ℕ+} [Field F] (v: Variable F) (off : CellOffset M W) : Table F M W Unit :=
  as_table_operation fun _ =>
  (TableOperation.Assign v off, ())

end Table

section Example
#eval!
  let p := 1009
  let p_prime := Fact.mk prime_1009
  let p_non_zero := Fact.mk (by norm_num : p ≠ 0)
  let p_large_enough := Fact.mk (by norm_num : p > 512)
  let asd : Table (F p) 3 1 _ := do
    let x <- Table.witness_cell ⟨0, 0⟩ (fun _ => (10 : F p))
    let y <- Table.witness_cell ⟨0, 1⟩ (fun _ => (20 : F p))
    let add8Inputs : (Add8.Inputs p).var := ⟨x, y⟩
    let z : Expression (F p) <- Table.subcircuit Add8.circuit add8Inputs
    let z_var : Variable (F p) := match z with
      | var v => v
      | _ => Variable.mk 42 (fun _ => 42)
    Table.assign z_var ⟨0, 2⟩
    return z
  asd.operations


end Example
