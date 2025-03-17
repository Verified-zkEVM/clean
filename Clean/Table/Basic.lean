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

variable {F : Type} {S : Type → Type} [ProvableType S]

@[table_norm]
def Row.get (row : Row F S) (i : Fin (size S)) : F :=
  let elems := to_elements row
  elems.get i

@[table_norm]
def Row.fill (element: F) : Row F S :=
  let elems := .fill (size S) element
  from_elements elems

@[table_norm]
def Row.findIdx? (row : Row F S) (prop: F → Bool) : Option (Fin (size S)) :=
  let elems := to_elements row
  elems.findIdx? prop

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
def TraceOfLength (F : Type) (S : Type → Type) [ProvableType S] (N : ℕ) : Type :=
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

variable {W: ℕ} {α: Type}

@[table_norm]
def fill (n: ℕ) (row: Row α S) : TraceOfLength α S n :=
  match n with
  | 0 => ⟨ <+>, rfl ⟩
  | n + 1 =>
    let t := fill n row
    ⟨ t.val +> row, by simp [t.prop, Trace.len] ⟩

def findIdx? {W: ℕ} (trace : TraceOfLength α S W) (prop : α → Bool) : Option (Fin W × Fin (size S)) :=
  match trace with
  | ⟨ <+>, _ ⟩ => none
  | ⟨ rest +> row, (h_rest : rest.len + 1 = W) ⟩ =>
    match row.findIdx? prop with
    | some j => some (⟨ rest.len, h_rest ▸ lt_add_one rest.len⟩, j)
    | none =>
      (findIdx? ⟨ rest, rfl ⟩ prop).map
        (fun ⟨i, j⟩ => (h_rest ▸ i.castSucc, j))

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

inductive Cell (W: ℕ+) (S : Type → Type) [ProvableType S] (N : ℕ) :=
  | input : CellOffset W S → Cell W S N
  | aux : Fin N → Cell W S N

/--
Mapping from cell offsets in the table to variable indices (or nothing, for empty cells).

The mapping must maintain the invariant that each variable is assigned to at most one cell.
-/
structure CellAssignment (W: ℕ+) (S : Type → Type) [ProvableType S] where
  offset : ℕ -- number of variables
  aux_length : ℕ -- number of auxiliary cells (i.e. those not part of the input/output layout)

  -- every variable is assigned to exactly one cell in the trace
  vars_to_cell : Vector (Cell W S aux_length) offset

  -- a cell (input / aux) is assigned a list of variables (that could be empty)
  input_to_vars : TraceOfLength (List (Fin offset)) S W
  aux_to_vars : Vector (List (Fin offset)) aux_length

  -- the mappings vars -> cells and cells -> vars are inverses of each other
  var_cell_var : ∀ var : Fin offset,
    match vars_to_cell.get var with
    | .input ⟨ i, j ⟩ => var ∈ input_to_vars.get i j
    | .aux i => var ∈ aux_to_vars.get i

  input_cell_var_cell : ∀ (i : Fin W) (j : Fin (size S)),
    ∀ var ∈ input_to_vars.get i j, vars_to_cell.get var = .input ⟨ i, j ⟩

  aux_cell_var_cell : ∀ (i : Fin aux_length),
    ∀ a ∈ aux_to_vars.get i, vars_to_cell.get a = .aux i

namespace CellAssignment
def empty (W: ℕ+) : CellAssignment W S where
  offset := 0
  aux_length := 0
  vars_to_cell := .nil
  input_to_vars := .fill W (.fill [])
  aux_to_vars := .nil
  var_cell_var := fun var => absurd var.is_lt var.val.not_lt_zero
  input_cell_var_cell := fun _ _ var _ => absurd var.is_lt var.val.not_lt_zero
  aux_cell_var_cell := fun _ var _ => absurd var.is_lt var.val.not_lt_zero

-- TODO: operations that modify a cell assignment while maintaining the invariants:
-- - add a new variable
-- - add a row of variables
-- - assign a variable from an aux cell to an input cell
-- - assign a variable from an input cell to a different input cell
end CellAssignment

/--
  Context of the TableConstraint that keeps track of the current state, this includes the underlying
  offset, and the current assignment of the variables to the cells in the trace.
-/
structure TableContext (W: ℕ+) (S : Type → Type) (F : Type) [Field F] [ProvableType S] where
  circuit : OperationsList F
  assignment : CellAssignment W S
  /-- invariant: the `circuit` and the `assignment` have the same number of variables -/
  offset_consistent : circuit.offset = assignment.offset

variable [Field F] {W: ℕ+} {α : Type}

/--
  An empty context has offset zero, and all variables are assigned by default to the first cell
-/
@[reducible]
def TableContext.empty : TableContext W S F where
  circuit := .from_offset 0
  assignment := .empty W
  offset_consistent := rfl

namespace TableContext
@[reducible]
def offset (table : TableContext W S F) : ℕ := table.assignment.offset

@[reducible]
def aux_length (table : TableContext W S F) : ℕ := table.assignment.aux_length

end TableContext

namespace TableConstraintOperation
-- /--
--   Returns the updated table context after applying the table operation
-- -/
-- @[table_norm]
-- def update_context {W: ℕ+} (ctx: TableContext W S F) :
--     TableConstraintOperation W S F → TableContext W S F
--   /-
--     Witnessing a fresh variable for a table offsets just increments the offset and add the mapping
--     from the variable index to the cell offset in the assignment mapping
--   -/
--   | Witness offset c => {
--       offset := ctx.offset + 1,
--       assignment := ctx.assignment.set offset ctx.offset,
--       operations := ctx.operations ++ [Witness offset c]
--     }

--   /-
--     Getting a row is equivalent to witnessing a fresh variable for each cell in the row
--   -/
--   | GetRow off => {
--       offset := ctx.offset + size S,
--       assignment := ctx.assignment.setRow off (.init (ctx.offset + ·)),
--       operations := ctx.operations ++ [GetRow off]
--     }

--   /-
--     Allocation of a sub-circuit moves the context offset by the witness length of the sub-circuit
--   -/
--   | Allocate subcircuit => {
--       offset := ctx.offset + subcircuit.witness_length,
--       assignment := ctx.assignment,
--       operations := ctx.operations ++ [Allocate subcircuit]
--     }

--   /-
--     Assigning a variable to a cell in the trace just updates the assignment mapping
--   -/
--   | Assign v offset => {
--       offset := ctx.offset,
--       assignment := ctx.assignment.set offset v.index,
--       operations := ctx.operations ++ [Assign v offset]
--     }
end TableConstraintOperation

@[reducible, table_norm]
def TableConstraint (W: ℕ+) (S : Type → Type) (F : Type) [Field F] [ProvableType S] :=
  StateM (TableContext W S F)

namespace TableConstraint
@[reducible]
def final_offset (table : TableConstraint W S F α) : ℕ :=
  table .empty |>.snd.circuit.offset

def operations (table : TableConstraint W S F α) : Operations F table.final_offset :=
  table .empty |>.snd.circuit.withLength

def assignment (table : TableConstraint W S F α) : CellAssignment W S :=
  table .empty |>.snd.assignment

/--
  A table constraint holds on a window of rows if the constraints hold on a suitable environment.
  In particular, we construct the environment by taking directly the result of the assignment function
  so that every variable evaluate to the trace cell value which is assigned to
-/
@[table_norm]
def constraints_hold_on_window (table : TableConstraint W S F Unit)
  (window: TraceOfLength F S W) (aux_env: Environment F) : Prop :=
  let ctx := table .empty |>.snd

  -- construct an env by simply taking the result of the assignment function
  let env : Environment F := ⟨ fun i =>
    if hi : i < ctx.offset then
      let x : Fin ctx.offset := ⟨i, hi⟩
      match ctx.assignment.vars_to_cell.get x with
      | .input ⟨i, j⟩ => window.get i j
      | .aux k =>  aux_env.get k
    else 0
  ⟩

  -- then we fold over allocated sub-circuits
  -- lifting directly to the soundness of the sub-circuit
  let operations := ctx.circuit.withLength
  Circuit.constraints_hold.soundness env operations

@[table_norm]
def output {α: Type} {W: ℕ+} (table : TableConstraint W S F α) : α :=
  table .empty |>.fst

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
