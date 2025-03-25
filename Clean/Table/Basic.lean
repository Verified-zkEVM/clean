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

@[table_norm, table_assignment_norm]
def Row.get (row : Row F S) (i : Fin (size S)) : F :=
  let elems := to_elements row
  elems.get i

@[table_norm]
def Row.fill (element: F) : Row F S :=
  let elems := .fill (size S) element
  from_elements elems

/- @[table_norm]
def Row.findIdx? (row : Row F S) (prop: F → Bool) : Option (Fin (size S)) :=
  let elems := to_elements row
  elems.findIdx? prop -/

/--
  A trace is an inductive list of rows. It can be viewed as a structured
  environment that maps cells to field elements.
-/
inductive Trace (F : Type) (S : Type → Type) [ProvableType S] where
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
@[table_norm, table_assignment_norm]
def len : Trace F S → ℕ
  | <+> => 0
  | rest +> _ => rest.len + 1

/--
  Get the row at a specific index in the trace, starting from the bottom of the trace
-/
@[table_assignment_norm]
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
@[table_assignment_norm]
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
@[table_assignment_norm]
def curr {W : ℕ+} (j : Fin (size S)) :  CellOffset W S := ⟨0, j⟩

/--
  Next row offset
-/
@[table_assignment_norm]
def next {W : ℕ+} (j : Fin (size S)) :  CellOffset W S := ⟨1, j⟩

end CellOffset

inductive Cell (W: ℕ+) (S : Type → Type) [ProvableType S] where
  | input : CellOffset W S → Cell W S
  | aux : ℕ → Cell W S

/--
Mapping between cell offsets in the table and variable indices.

The mapping must maintain the invariant that each variable is assigned to at most one cell.
On the other hand, a cell can be assigned zero, one or more variables.
-/
structure CellAssignment (W: ℕ+) (S : Type → Type) [ProvableType S] where
  offset : ℕ -- number of variables
  aux_length : ℕ -- number of auxiliary cells (i.e. those not part of the input/output layout)

  /-- every variable is assigned to exactly one cell in the trace -/
  vars : Vector (Cell W S) offset

variable {W: ℕ+}

namespace CellAssignment
@[table_assignment_norm]
def get (assignment: CellAssignment W S) (var: Fin assignment.offset) : Cell W S :=
  assignment.vars.get var

@[table_assignment_norm, reducible]
def empty (W: ℕ+) : CellAssignment W S where
  offset := 0
  aux_length := 0
  vars := #v[]

@[table_assignment_norm]
def push_var_aux (assignment: CellAssignment W S) : CellAssignment W S :=
  {
    offset := assignment.offset + 1
    aux_length := assignment.aux_length + 1
    vars := assignment.vars.push (.aux assignment.aux_length)
  }

@[table_assignment_norm]
def push_vars_aux (assignment: CellAssignment W S) : ℕ → CellAssignment W S
  | 0 => assignment
  | n + 1 => (assignment.push_vars_aux n).push_var_aux

lemma push_vars_aux_offset (assignment: CellAssignment W S) (n : ℕ) :
  (assignment.push_vars_aux n).offset = assignment.offset + n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [push_vars_aux]
    simp_arith [push_var_aux, ih]

@[table_assignment_norm]
def push_var_input (assignment: CellAssignment W S) (row: Fin W) (col: Fin (size S)) : CellAssignment W S :=
  {
    offset := assignment.offset + 1
    aux_length := assignment.aux_length
    vars := assignment.vars.push (.input ⟨ row, col ⟩)
  }

def push_var_input_offset (assignment: CellAssignment W S) (row: Fin W) (col: Fin (size S)) :
  (assignment.push_var_input row col).offset = assignment.offset + 1 := by
  simp [push_var_input, Vector.push]

def foldRange (n : ℕ) (f : α → Fin n → α) (init : α) : α := List.finRange n |>.foldl f init

def foldRange_succ (n : ℕ) (f : α → Fin (n + 1) → α) (init : α) :
  foldRange (n + 1) f init = f (foldRange n (fun acc i => f acc i.castSucc) init) (.last n) := by
  rw [foldRange, foldRange, List.finRange_succ_last, List.foldl_concat, List.foldl_map]

@[table_assignment_norm]
def push_row (assignment: CellAssignment W S) (row: Fin W) : CellAssignment W S :=
  foldRange (size S) (fun assignment col => push_var_input assignment row col) assignment

lemma push_row_offset (assignment: CellAssignment W S) (row: Fin W) :
  (assignment.push_row row).offset = assignment.offset + size S := by
  -- generalize goal to enable induction
  suffices ∀ n : ℕ, (hs : n ≤ size S) →
    (foldRange n (fun assignment col ↦ assignment.push_var_input row ⟨col, by linarith [col.is_lt]⟩) assignment).offset = assignment.offset + n
    by apply this; rfl
  intro n
  induction n with
  | zero => simp [foldRange]
  | succ n ih =>
    intro hs
    specialize ih (by linarith)
    rw [foldRange_succ, push_var_input_offset]
    simp only [Fin.coe_castSucc]
    rw [ih]
    ac_rfl

@[table_assignment_norm]
def set_var_input (assignment: CellAssignment W S) (row: Fin W) (col: Fin (size S)) (var: ℕ) : CellAssignment W S :=
  let vars := assignment.vars.set? var (.input ⟨ row, col ⟩)
  { assignment with vars }
end CellAssignment

/--
  Context of the TableConstraint that keeps track of the current state, this includes the underlying
  offset, and the current assignment of the variables to the cells in the trace.
-/
structure TableContext (W: ℕ+) (S : Type → Type) (F : Type) [Field F] [ProvableType S] where
  circuit : OperationsList F
  assignment : CellAssignment W S

variable [Field F]  {α : Type}

namespace TableContext
@[reducible, table_norm, table_assignment_norm]
def empty : TableContext W S F where
  circuit := .from_offset 0
  assignment := .empty W

@[reducible, table_norm, table_assignment_norm]
def offset (table : TableContext W S F) : ℕ := table.circuit.offset

@[reducible, table_assignment_norm]
def aux_length (table : TableContext W S F) : ℕ := table.assignment.aux_length
end TableContext

@[reducible, table_norm, table_assignment_norm]
def TableConstraint (W: ℕ+) (S : Type → Type) (F : Type) [Field F] [ProvableType S] :=
  StateM (TableContext W S F)

@[table_assignment_norm]
def assignment_from_circuit {n} (as: CellAssignment W S) : Operations F n → CellAssignment W S
  | .empty _ => as
  | .witness ops m _ => (assignment_from_circuit as ops).push_vars_aux m
  | .assert ops _ => assignment_from_circuit as ops
  | .lookup ops _ => assignment_from_circuit as ops
  | .subcircuit ops s => (assignment_from_circuit as ops).push_vars_aux s.local_length

@[reducible, table_norm, table_assignment_norm]
instance : MonadLift (Circuit F) (TableConstraint W S F) where
  monadLift circuit ctx :=
    let (a, ops) := circuit ctx.circuit

    -- the updated assignment is computed from a fresh starting circuit, independent of the circuit so far
    -- (if we would use `ops` instead of `circuit.operations 0`, we would be redoing previous assignments)
    let assignment := assignment_from_circuit (F:=F) ctx.assignment (circuit.operations 0)

    (a, { circuit := ops, assignment })

namespace TableConstraint
@[reducible, table_norm, table_assignment_norm]
def final_offset (table : TableConstraint W S F α) : ℕ :=
  table .empty |>.snd.circuit.offset

@[table_norm]
def operations (table : TableConstraint W S F α) : Operations F table.final_offset :=
  table .empty |>.snd.circuit.withLength

@[table_assignment_norm]
def final_assignment (table : TableConstraint W S F α) : CellAssignment W S :=
  table .empty |>.snd.assignment

@[table_assignment_norm]
def offset_consistent (table : TableConstraint W S F α) : Prop :=
  table.final_offset = table.final_assignment.offset

-- construct an env by taking the result of the assignment function for input/output cells,
-- and allowing arbitrary values for aux cells and invalid variables
def window_env (table : TableConstraint W S F Unit)
  (window: TraceOfLength F S W) (aux_env : Environment F) : Environment F :=
  let ctx := table .empty |>.snd
  .mk fun i =>
    if hi : i < ctx.assignment.offset then
      match ctx.assignment.vars.get ⟨i, hi⟩ with
      | .input ⟨i, j⟩ => window.get i j
      | .aux k => aux_env.get k
    else aux_env.get (i + ctx.assignment.aux_length)

/--
  A table constraint holds on a window of rows if the constraints hold on a suitable environment.
  In particular, we construct the environment by taking directly the result of the assignment function
  so that every variable evaluate to the trace cell value which is assigned to
-/
@[table_norm]
def constraints_hold_on_window (table : TableConstraint W S F Unit)
  (window: TraceOfLength F S W) (aux_env : Environment F) : Prop :=
  let env := window_env table window aux_env
  Circuit.constraints_hold.soundness env table.operations

@[table_norm]
def output {α: Type} {W: ℕ+} (table : TableConstraint W S F α) : α :=
  table .empty |>.fst

/--
  Get a fresh variable for each cell in a given row
-/
@[table_norm, table_assignment_norm]
def get_row {W: ℕ+} (row : Fin W) : TableConstraint W S F (Var S F) :=
  modifyGet fun ctx =>
    let vars := Vector.init (fun i => ⟨ctx.offset + i⟩)
    let exprs := vars.map Expression.var
    let ctx' : TableContext W S F := {
      circuit := ctx.circuit.witness (size S) (fun eval => exprs.map eval),
      assignment := ctx.assignment.push_row row
    }
    (from_vars exprs, ctx')

/--
  Get a fresh variable for each cell in the current row
-/
@[table_norm, table_assignment_norm]
def get_curr_row {W: ℕ+} : TableConstraint W S F (Var S F) := get_row 0

/--
  Get a fresh variable for each cell in the next row
-/
@[table_norm, table_assignment_norm]
def get_next_row {W: ℕ+} : TableConstraint W S F (Var S F) := get_row 1

@[table_assignment_norm]
def assign_var {W: ℕ+} (off : CellOffset W S) (v : Variable F) : TableConstraint W S F Unit :=
  modify fun ctx =>
    let assignment := ctx.assignment.set_var_input off.rowOffset off.column v.index
    { ctx with assignment }

@[table_norm, table_assignment_norm]
theorem assign_var_circuit : ∀ ctx (off : CellOffset W S) (v : Variable F),
  (assign_var off v ctx).snd.circuit = ctx.circuit := by intros; rfl

@[table_norm, table_assignment_norm]
def assign {W: ℕ+} (off : CellOffset W S) : Expression F → TableConstraint W S F Unit
  -- a variable is assigned directly
  | .var v => assign_var off v
  -- a composed expression or constant is first stored in a new variable, which is assigned
  | x => do
    let new_var ← witness_var x.eval
    assert_zero (x - var new_var)
    assign_var off new_var

@[table_norm, table_assignment_norm]
def assign_next_row {W: ℕ+} (next : Var S F) : TableConstraint W S F Unit :=
  let vars := to_vars next
  for i in List.finRange (size S) do
    assign (.next i) (vars.get i)
end TableConstraint

export TableConstraint (get_curr_row get_next_row assign assign_next_row)

@[reducible]
def SingleRowConstraint (S : Type → Type) (F : Type) [Field F] [ProvableType S] := TableConstraint 1 S F Unit

@[reducible]
def TwoRowsConstraint (S : Type → Type) (F : Type) [Field F] [ProvableType S] := TableConstraint 2 S F Unit

inductive TableOperation (S : Type → Type) (F : Type) [Field F] [ProvableType S] where
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
def table_constraints_hold {N : ℕ} (constraints : List (TableOperation S F))
  (trace: TraceOfLength F S N) (env: ℕ → ℕ → Environment F) : Prop :=
  let constraints_and_envs := constraints.mapIdx (fun i cs => (cs, env i))
  foldl constraints_and_envs trace.val constraints_and_envs
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
  foldl (cs : List (TableOperation S F × (ℕ → (Environment F)))) :
    Trace F S → (cs_iterator: List (TableOperation S F × (ℕ → (Environment F)))) → Prop
    -- if the trace has at least two rows and the constraint is a "every row except last" constraint, we apply the constraint
    | trace +> curr +> next, (⟨.EveryRowExceptLast constraint, env⟩)::rest =>
        let others := foldl cs (trace +> curr +> next) rest
        let window : TraceOfLength F S 2 := ⟨<+> +> curr +> next, rfl ⟩
        constraint.constraints_hold_on_window window (env (trace.len + 1)) ∧ others

    -- if the trace has at least one row and the constraint is a boundary constraint, we apply the constraint if the
    -- index is the same as the length of the remaining trace
    | trace +> row, (⟨.Boundary idx constraint, env⟩)::rest =>
        let others := foldl cs (trace +> row) rest
        let window : TraceOfLength F S 1 := ⟨<+> +> row, rfl⟩
        if trace.len = idx then constraint.constraints_hold_on_window window (env trace.len) ∧ others else others

    -- if the trace has at least one row and the constraint is a "every row" constraint, we apply the constraint
    | trace +> row, (⟨.EveryRow constraint, env⟩)::rest =>
        let others := foldl cs (trace +> row) rest
        let window : TraceOfLength F S 1 := ⟨<+> +> row, rfl⟩
        constraint.constraints_hold_on_window window (env trace.len) ∧ others

    -- if the trace has not enough rows for the "every row except last" constraint, we skip the constraint
    | trace, (⟨.EveryRowExceptLast _, _⟩)::rest =>
        foldl cs trace rest

    -- if the cs_iterator is empty, we start again with the initial constraints on the next row
    | trace +> _, [] =>
        foldl cs trace cs

    -- if the trace is empty, we are done
    | <+>, _ => True


structure FormalTable (F : Type) [Field F] (S : Type → Type) [ProvableType S] where
  /-- list of constraints that are applied over the table -/
  constraints : List (TableOperation S F)

  /-- optional assumption on the table length -/
  assumption : ℕ → Prop := fun _ => True

  /-- specification for the table -/
  spec {N : ℕ} : TraceOfLength F S N → Prop

  /-- the soundness states that if the assumptions hold, then
      the constraints hold implies that the spec holds. -/
  soundness :
    ∀ (N : ℕ) (trace: TraceOfLength F S N) (env: ℕ → ℕ → Environment F),
    assumption N →
    table_constraints_hold constraints trace env →
    spec trace

  /-- this property tells us that that the number of variables contained in the `assignment` of each
      constraint is consistent with the number of variables introduced in the circuit. -/
  offset_consistent :
    constraints.Forall fun cs =>
      match cs with
      | .Boundary _ constraint => constraint.offset_consistent
      | .EveryRow constraint => constraint.offset_consistent
      | .EveryRowExceptLast constraint => constraint.offset_consistent
    := by rfl


-- add some important lemmas to simp sets
attribute [table_norm] size from_elements to_elements to_vars from_vars
attribute [table_assignment_norm] to_elements
attribute [table_norm] Circuit.constraints_hold.soundness

attribute [table_norm, table_assignment_norm] liftM monadLift
attribute [table_norm, table_assignment_norm] bind StateT.bind
attribute [table_norm, table_assignment_norm] modify modifyGet MonadStateOf.modifyGet StateT.modifyGet
