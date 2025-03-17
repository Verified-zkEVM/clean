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

end TraceOfLength
variable {W: ℕ} {α: Type}

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
  input_to_vars : Matrix (List (Fin offset)) W (size S)
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

variable {W: ℕ+}

namespace CellAssignment
def empty (W: ℕ+) : CellAssignment W S where
  offset := 0
  aux_length := 0
  vars_to_cell := .nil
  input_to_vars := .fill W (size S) []
  aux_to_vars := .nil
  var_cell_var := fun var => absurd var.is_lt var.val.not_lt_zero
  input_cell_var_cell := fun _ _ var _ => absurd var.is_lt var.val.not_lt_zero
  aux_cell_var_cell := fun _ var _ => absurd var.is_lt var.val.not_lt_zero

def push_var_input (assignment: CellAssignment W S) (row: Fin W) (col: Fin (size S)) : CellAssignment W S :=
  let index := assignment.offset
  let cell := Cell.input ⟨ row, col ⟩
  let fin_index : Fin (assignment.offset + 1) := ⟨ index, by linarith ⟩
  let input_to_vars' := assignment.input_to_vars.map (fun l => l.map Fin.castSucc)
  let input_to_vars := input_to_vars'.set row col <| input_to_vars'.get row col ++ [fin_index]
  let aux_to_vars := assignment.aux_to_vars.map (fun l => l.map Fin.castSucc)
  {
    offset := assignment.offset + 1
    aux_length := assignment.aux_length
    vars_to_cell := assignment.vars_to_cell.push cell
    input_to_vars := input_to_vars
    aux_to_vars := aux_to_vars
    var_cell_var := by
      intro var
      have h_len : assignment.vars_to_cell.val.length = assignment.offset := by simp
      by_cases h : var.val < assignment.offset
      have : (assignment.vars_to_cell.push cell).get var = assignment.vars_to_cell.get ⟨ var, h ⟩ := by
        simp [Vector.push]
        exact List.getElem_append var.val (by linarith)
      rw [this]
      clear this
      have ih := assignment.var_cell_var ⟨ var, h ⟩
      split
      next x i j heq =>
        rw [heq] at ih
        simp only at ih
        clear heq
        suffices h : var ∈ input_to_vars'.get i j by
          simp [input_to_vars]
          sorry -- TODO
        simp [input_to_vars']
        use ⟨ var, h ⟩
        use ih
        simp
      next x i j heq =>
        rw [heq] at ih
        simp at ih
        clear heq
        simp [aux_to_vars]
        use ⟨ var, h ⟩
        use ih
        simp
      have var_eq : var.val = assignment.offset := by linarith [var.is_lt]
      have : (assignment.vars_to_cell.push cell).get var = cell := by
        simp [Vector.push, var_eq]
      rw [this]; simp only
      simp [input_to_vars]
      right
      ext
      simp [fin_index, index, var_eq]

    input_cell_var_cell := by sorry
    aux_cell_var_cell := by
      intro aux var h_var
      by_cases h : var.val < assignment.offset
      have ih := assignment.aux_cell_var_cell aux ⟨ var, h ⟩
      sorry
      sorry
  }

def push_var_default_input (assignment: CellAssignment W S) (lt: assignment.offset < W * (size S)) : CellAssignment W S :=
  let index := assignment.offset
  have nonempty : size S > 0 := by
      by_contra h'
      have eq_zero : size S = 0 := by linarith
      simp [eq_zero] at lt
  let row : Fin W := ⟨ index / size S, (Nat.div_lt_iff_lt_mul nonempty).mpr lt⟩
  let col : Fin (size S) := ⟨ index % size S, Nat.mod_lt index nonempty ⟩
  push_var_input assignment row col

def push_var_default_aux (assignment: CellAssignment W S) (lt: assignment.offset ≥ W * (size S)) : CellAssignment W S :=
  sorry

def push_var_default_cell (assignment: CellAssignment W S) : CellAssignment W S :=
  if h: assignment.offset < W * (size S) then
    push_var_default_input assignment h
  else
    push_var_default_aux assignment (Nat.ge_of_not_lt h)

def default_from_offset (W: ℕ+) (offset : ℕ) : CellAssignment W S :=
  (Vector.finRange offset).val.foldl (fun acc _ => push_var_default_cell acc) (.empty W)

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
  /-- also, circuit has to start from a zero offset -/
  offset_zero : circuit.withLength.initial_offset = 0

variable [Field F]  {α : Type}

namespace TableContext
/--
  An empty context has offset zero, and all variables are assigned by default to the first cell
-/
@[reducible]
def empty : TableContext W S F where
  circuit := .from_offset 0
  assignment := .empty W
  offset_consistent := rfl
  offset_zero := rfl

@[reducible]
def offset (table : TableContext W S F) : ℕ := table.assignment.offset

@[reducible]
def aux_length (table : TableContext W S F) : ℕ := table.assignment.aux_length

@[table_norm]
def from_circuit (ops: OperationsList F) (h_initial : ops.withLength.initial_offset = 0) :
  ∃ ctx: TableContext W S F, ctx.circuit = ops :=
  match ops with
  | ⟨_, .empty 0⟩ => ⟨.empty, rfl⟩
  | ⟨_, .witness ops m c⟩ =>
    let ⟨prev, h⟩ := from_circuit ops h_initial
    let assignment := sorry
    ⟨{ prev with
      circuit := prev.circuit.witness m c
      assignment
      offset_consistent := by sorry
    }, by simp [h]⟩
  | ⟨_, .assert ops e⟩ =>
    let ⟨prev, h⟩ := from_circuit ops h_initial
    ⟨{ prev with circuit := prev.circuit.assert e }, by simp [h]⟩
  | ⟨_, .lookup ops l⟩ =>
    let ⟨prev, h⟩ := from_circuit ops h_initial
    ⟨{ prev with circuit := prev.circuit.lookup l }, by simp [h]⟩
  | ⟨_, .subcircuit ops s⟩ =>
    let ⟨prev, h⟩ := from_circuit ops h_initial
    let subcircuit : SubCircuit F prev.circuit.offset := cast (by rw [h]) s
    let assignment := sorry
    ⟨{ prev with
      circuit := prev.circuit.subcircuit subcircuit
      assignment
      offset_consistent := by sorry
    }, by
      simp [h, subcircuit]
      constructor <;> {
        congr
        repeat rw [h]
        apply cast_heq
      }
    ⟩
end TableContext

-- namespace TableConstraintOperation
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
-- end TableConstraintOperation

@[reducible, table_norm]
def TableConstraint (W: ℕ+) (S : Type → Type) (F : Type) [Field F] [ProvableType S] :=
  StateM (TableContext W S F)

instance : MonadLift (Circuit F) (TableConstraint W S F) where
  monadLift circuit ctx :=
    let result := circuit ctx.circuit
    let ⟨table_ctx, h⟩ := TableContext.from_circuit result.snd (by
      sorry
    )
    (result.fst, .from_circuit ctx')

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
