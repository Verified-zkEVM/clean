import Mathlib.Algebra.Field.Basic
import Mathlib.Data.ZMod.Basic
import Clean.Utils.Primes
import Clean.Utils.Vector
import Clean.Circuit.Basic
import Clean.Circuit.SubCircuit
import Clean.Circuit.Expression
import Clean.Circuit.Provable
import Clean.Utils.Field
import Clean.Table.SimpTable

/--
  A row is StructuredElement that contains field elements.
-/
@[reducible]
def Row (F : Type) (S : Type → Type) [ProvableType S] := S F

variable {F : Type} {S : Type → Type} [NonEmptyProvableType S]

@[table_norm]
def Row.get (row : Row F S) (i : Fin (size S)) : F :=
  let elems := to_elements row
  elems.get i

/--
  A trace is an inductive list of rows. It can be viewed as a structured
  environment that maps cells to field elements.
-/
inductive Trace (F : Type) (S : Type → Type) [ProvableType S] :=
  /-- An empty trace -/
  | empty : Trace F S
  /-- Add a row to the end of the trace -/
  | cons (rest: Trace F S) (row: Row F S) : Trace F S

@[inherit_doc] notation:67 "<+>" => Trace.empty
@[inherit_doc] infixl:67 " +> " => Trace.cons

namespace Trace
/--
  The length of a trace is the number of rows it contains.
-/
@[table_norm]
def len : Trace F S → ℕ
  | <+> => 0
  | rest +> _ => rest.len + 1

/--
  Get the row at a specific index in the trace, starting from the bottom of the trace
-/
@[table_norm]
def getLeFromBottom :
    (trace : Trace F S) → (row : Fin trace.len) → (col : Fin (size S)) → F
  | _ +> currRow, ⟨0, _⟩, j => currRow.get j
  | rest +> _, ⟨i + 1, h⟩, j => getLeFromBottom rest ⟨i, Nat.le_of_succ_le_succ h⟩ j

end Trace


/--
  A trace of length N is a trace with exactly N rows.
-/
def TraceOfLength (F : Type) (S : Type → Type) [NonEmptyProvableType S] (N : ℕ) : Type :=
  { env : Trace F S // env.len = N }

namespace TraceOfLength

/--
  Get the row at a specific index in the trace, starting from the top
-/
@[table_norm]
def get {M : ℕ} :
    (env : TraceOfLength F S M) → (i : Fin M) → (j : Fin (size S)) → F
  | ⟨env, h⟩, i, j => env.getLeFromBottom ⟨
      M - 1 - i,
      by rw [h]; apply Nat.sub_one_sub_lt_of_lt; exact i.is_lt
    ⟩ j

/--
  Apply a proposition to every row in the trace
-/
@[table_norm]
def forAllRowsOfTrace {N : ℕ}
    (trace : TraceOfLength F S N) (prop : Row F S → Prop) : Prop :=
  inner trace.val prop
  where
  @[table_norm]
  inner : Trace F S → (Row F S → Prop) → Prop
    | <+>, _ => true
    | rest +> row, prop => prop row ∧ inner rest prop

/--
  Apply a proposition to every row in the trace except the last one
-/
@[table_norm]
def forAllRowsOfTraceExceptLast {N : ℕ}
    (trace : TraceOfLength F S N) (prop : Row F S → Prop) : Prop :=
  inner trace.val prop
  where
  inner : Trace F S → (Row F S → Prop) → Prop
    | <+>, _ => true
    | <+> +> _, _ => true
    | rest +> curr +> _, prop => prop curr ∧ inner (rest +> curr) prop


/--
  Apply a proposition, which could be dependent on the row index, to every row of the trace
-/
@[table_norm]
def forAllRowsOfTraceWithIndex {N : ℕ}
    (trace : TraceOfLength F S N) (prop : Row F S → ℕ → Prop) : Prop :=
  inner trace.val prop
  where
  @[table_norm]
  inner : Trace F S → (Row F S → ℕ → Prop) → Prop
    | <+>, _ => true
    | rest +> row, prop => (prop row rest.len) ∧ inner rest prop

end TraceOfLength

/--
  A cell offset is an offset in a table that points to a specific cell in a row.
  It is used to define a relative position in the trace.
  `W` is the size of the "vertical window", which means that we can reference at most
  `W` rows above the current row.
  To make sure that the vertical offset is bounded, it is represented as a `Fin W`.
-/
structure CellOffset (W: ℕ+) (S : Type → Type) [ProvableType S]  where
  rowOffset: Fin W
  column: Fin (size S)
deriving Repr

namespace CellOffset

/--
  Current row offset
-/
@[table_norm]
def curr {W : ℕ+} (j : Fin (size S)) :  CellOffset W S := ⟨0, j⟩

/--
  Next row offset
-/
@[table_norm]
def next {W : ℕ+} (j : Fin (size S)) :  CellOffset W S := ⟨1, j⟩

end CellOffset

/--
  Mapping from the index of a variable to a cell offset in the table.
-/
@[reducible]
def CellAssignment (W: ℕ+) (S : Type → Type) [ProvableType S] := ℕ → CellOffset W S

/--
  Atomic operations for constructing a table constraint, which is a constraint applied to a window
  of rows in a table.
-/
inductive TableConstraintOperation (W : ℕ+) (S : Type → Type) (F : Type) [Field F] [ProvableType S] where
  /--
    Add some witnessed variable to the context
  -/
  | Witness : CellOffset W S → (compute : Unit → F) → TableConstraintOperation W S F

  /--
    Witness a fresh variable for each cell in the row at some offset `off` in the trace
  -/
  | GetRow : (off : Fin W) → TableConstraintOperation W S F

  /--
    Allocate a subcircuit in the trace
  -/
  | Allocate: {n: ℕ} → SubCircuit F n → TableConstraintOperation W S F

  /--
    Assign a variable to a cell in the trace
  -/
  | Assign : Variable F → CellOffset W S → TableConstraintOperation W S F

/--
  Context of the TableConstraint that keeps track of the current state, this includes the underlying
  offset, and the current assignment of the variables to the cells in the trace.
-/
structure TableContext (W: ℕ+) (S : Type → Type) (F : Type) [Field F] [ProvableType S] where
  offset: ℕ
  assignment : CellAssignment W S
  operations: List (TableConstraintOperation W S F)

variable [Field F]

/--
  An empty context has offset zero, and all variables are assigned by default to the first cell
-/
@[reducible]
def TableContext.empty {W: ℕ+} : TableContext W S F := {
  offset := 0,
  -- TODO: is there a better way?
  assignment := fun _ => ⟨0, ⟨0, NonEmptyProvableType.nonempty⟩⟩,
  operations := []
}

namespace TableConstraintOperation

/--
  Returns the updated table context after applying the table operation
-/
@[table_norm]
def update_context {W: ℕ+} (ctx: TableContext W S F) :
    TableConstraintOperation W S F → TableContext W S F
  /-
    Witnessing a fresh variable for a table offsets just increments the offset and add the mapping
    from the variable index to the cell offset in the assignment mapping
  -/
  | Witness offset c => {
      offset := ctx.offset + 1,
      assignment := fun x => if x = ctx.offset then offset else ctx.assignment x,
      operations := ctx.operations ++ [Witness offset c]
    }

  /-
    Getting a row is equivalent to witnessing a fresh variable for each cell in the row
  -/
  | GetRow off => {
      offset := ctx.offset + size S,
      assignment := fun x => if h : x >= ctx.offset && x < ctx.offset + size S then ⟨off, ⟨x-ctx.offset, by
        simp only [ge_iff_le, Bool.and_eq_true, decide_eq_true_eq] at h
        omega
      ⟩⟩ else ctx.assignment x,
      operations := ctx.operations ++ [GetRow off]
    }

  /-
    Allocation of a sub-circuit moves the context offset by the witness length of the sub-circuit
  -/
  | Allocate subcircuit => {
      offset := ctx.offset + subcircuit.witness_length,
      assignment := ctx.assignment,
      operations := ctx.operations ++ [Allocate subcircuit]
    }

  /-
    Assigning a variable to a cell in the trace just updates the assignment mapping
  -/
  | Assign v offset => {
      offset := ctx.offset,
      assignment := fun x => if x = v.index then offset else ctx.assignment x,
      operations := ctx.operations ++ [Assign v offset]
    }

instance {W: ℕ+} [Repr F] :
    ToString (TableConstraintOperation W S F) where
  toString
    | Witness offset _ => "(Witness " ++ reprStr offset ++ ")"
    | GetRow off => "(GetRow " ++ reprStr off ++ ")"
    | Allocate {ops, ..} => "(Allocate " ++ reprStr ops ++ ")"
    | Assign v offset => "(Assign " ++ reprStr v ++ " " ++ reprStr offset ++ ")"

end TableConstraintOperation

@[reducible, table_norm]
def TableConstraint (W: ℕ+) (S : Type → Type) (F : Type) [Field F] [NonEmptyProvableType S] :=
  StateM (TableContext W S F)

namespace TableConstraint
def operations {α: Type} {W: ℕ+} (table : TableConstraint W S F α):
    List (TableConstraintOperation W S F) :=
  table .empty |>.snd.operations

def assignment {α: Type} {W: ℕ+} (table : TableConstraint W S F α):
    CellAssignment W S :=
  table .empty |>.snd.assignment

/--
  A table constraint holds on a window of rows if the constraints hold on a suitable environment.
  In particular, we construct the environment by taking directly the result of the assignment function
  so that every variable evaluate to the trace cell value which is assigned to
-/
@[table_norm]
def constraints_hold_on_window {W : ℕ+}
    (table : TableConstraint W S F Unit) (window: TraceOfLength F S W) : Prop :=
  let ctx := table .empty |>.snd

  -- construct an env by simply taking the result of the assignment function
  let env : Environment F := ⟨ fun x =>
    match ctx.assignment x with
    | ⟨i, j⟩ => window.get i j
  ⟩

  -- then we fold over allocated sub-circuits
  -- lifting directly to the soundness of the sub-circuit
  foldl ctx.operations env
  where
  @[table_norm]
  foldl : List (TableConstraintOperation W S F) → (env: Environment F) → Prop
  | [], _ => true
  | op :: ops, env =>
    match op with
    | .Allocate {soundness ..} => soundness env ∧ foldl ops env
    | _ => foldl ops env

@[table_norm]
def output {α: Type} {W: ℕ+} (table : TableConstraint W S F α) : α :=
  table .empty |>.fst

open TableConstraintOperation (update_context)

@[table_norm]
def witness_cell {W: ℕ+}
    (off : CellOffset W S) (compute : Unit → F) : TableConstraint W S F (Variable F) :=
  modifyGet fun ctx =>
    (⟨ ctx.offset ⟩, update_context ctx (.Witness off compute))

@[table_norm]
def get_cell {W: ℕ+}
    (off : CellOffset W S): TableConstraint W S F (Variable F) :=
  modifyGet fun ctx =>
    (⟨ ctx.offset ⟩, update_context ctx (.Witness off (fun _ => 0)))

/--
  Get a fresh variable for each cell in the current row
-/
@[table_norm]
def get_curr_row {W: ℕ+} : TableConstraint W S F (Var S F) :=
  modifyGet fun ctx =>
    let vars := Vector.init (fun i => ⟨ctx.offset + i⟩)
    let exprs := vars.map Expression.var
    (from_vars exprs, update_context ctx (.GetRow 0))

/--
  Get a fresh variable for each cell in the next row
-/
@[table_norm]
def get_next_row {W: ℕ+} : TableConstraint W S F (Var S F) :=
  modifyGet fun ctx =>
    let vars := Vector.init (fun i => ⟨ctx.offset + i⟩)
    let exprs := vars.map Expression.var
    (from_vars exprs, update_context ctx (.GetRow 1))

def subcircuit {W: ℕ+} {α β : TypeMap} [ProvableType β] [ProvableType α]
    (circuit: FormalCircuit F β α) (b: Var β F) : TableConstraint W S F (Var α F) :=
  modifyGet fun ctx =>
    let ⟨ a, subcircuit ⟩ := Circuit.formal_circuit_to_subcircuit ctx.offset circuit b
    (a, update_context ctx (.Allocate subcircuit))

def assertion {W: ℕ+} {β : TypeMap} [ProvableType β]
    (circuit: FormalAssertion F β) (b: Var β F) : TableConstraint W S F Unit :=
  modify fun ctx =>
    let subcircuit := Circuit.formal_assertion_to_subcircuit ctx.offset circuit b
    update_context ctx (.Allocate subcircuit)

@[table_norm]
def assign {W: ℕ+} (v: Variable F) (off : CellOffset W S) : TableConstraint W S F Unit :=
  modify fun ctx =>
    update_context ctx (.Assign v off)

attribute [table_norm] size
attribute [table_norm] to_elements
attribute [table_norm] from_elements
attribute [table_norm] to_vars
attribute [table_norm] from_vars
end TableConstraint


@[reducible]
def SingleRowConstraint (S : Type → Type) (F : Type) [Field F] [NonEmptyProvableType S] := TableConstraint 1 S F Unit

@[reducible]
def TwoRowsConstraint (S : Type → Type) (F : Type) [Field F] [NonEmptyProvableType S] := TableConstraint 2 S F Unit

inductive TableOperation (S : Type → Type) (F : Type) [Field F] [NonEmptyProvableType S] where
  /--
    A `Boundary` constraint is a constraint that is applied only to a specific row
  -/
  | Boundary: ℕ → SingleRowConstraint S F → TableOperation S F

  /--
    An `EveryRow` constraint is a constraint that is applied to every row.
    It can only reference cells on the same row
  -/
  | EveryRow: SingleRowConstraint S F → TableOperation S F

  /--
    An `EveryRowExceptLast` constraint is a constraint that is applied to every row except the last.
    It can reference cells from the current row, or the next row.

    Note that this will not apply any constraints to a trace of length one.
  -/
  | EveryRowExceptLast: TwoRowsConstraint S F → TableOperation S F


/--
  The constraints hold over a trace if the hold individually in a suitable environment, where the
  environment is derived from the `CellAssignment` functions. Intuitively, if a variable `x`
  is assigned to a field element in the trace `y: F` using a `CellAssignment` function, then ` env x = y`
-/
@[table_norm]
def table_constraints_hold {N : ℕ}
    (constraints : List (TableOperation S F)) (trace: TraceOfLength F S N) : Prop :=
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
  @[table_norm]
  foldl (cs : List (TableOperation S F)) : Trace F S → (cs_iterator: List (TableOperation S F)) → Prop
    -- if the trace has at least two rows and the constraint is a "every row except last" constraint, we apply the constraint
    | trace +> curr +> next, (TableOperation.EveryRowExceptLast constraint)::rest =>
        let others := foldl cs (trace +> curr +> next) rest
        let window : TraceOfLength F S 2 := ⟨<+> +> curr +> next, rfl ⟩
        constraint.constraints_hold_on_window window ∧ others

    -- if the trace has at least one row and the constraint is a boundary constraint, we apply the constraint if the
    -- index is the same as the length of the remaining trace
    | trace +> row, (TableOperation.Boundary idx constraint)::rest =>
        let others := foldl cs (trace +> row) rest
        let window : TraceOfLength F S 1 := ⟨<+> +> row, rfl⟩
        if trace.len = idx then constraint.constraints_hold_on_window window ∧ others else others

    -- if the trace has at least one row and the constraint is a "every row" constraint, we apply the constraint
    | trace +> row, (TableOperation.EveryRow constraint)::rest =>
        let others := foldl cs (trace +> row) rest
        let window : TraceOfLength F S 1 := ⟨<+> +> row, rfl⟩
        constraint.constraints_hold_on_window window ∧ others

    -- if the trace has not enough rows for the "every row except last" constraint, we skip the constraint
    | trace, (TableOperation.EveryRowExceptLast _)::rest =>
        foldl cs trace rest

    -- if the cs_iterator is empty, we start again with the initial constraints on the next row
    | trace +> _, [] =>
        foldl cs trace cs

    -- if the trace is empty, we are done
    | <+>, _ => True


structure FormalTable (F : Type) [Field F] (S : Type → Type) [NonEmptyProvableType S] where
  -- list of constraints that are applied over the table
  constraints : List (TableOperation S F)

  -- optional assumption on the table length
  assumption : ℕ → Prop := fun _ => True

  -- specification for the table
  spec {N : ℕ} : TraceOfLength F S N → Prop

  -- the soundness states that if the assumptions hold, then
  -- the constraints hold implies that the spec holds
  soundness :
    ∀ (N : ℕ) (trace: TraceOfLength F S N),
    assumption N →
    table_constraints_hold constraints trace →
    spec trace
