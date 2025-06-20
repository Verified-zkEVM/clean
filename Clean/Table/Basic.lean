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

@[table_norm]
def lastRow : (trace : Trace F S) → (hlen : trace.len > 0) → S F
  | <+>, h  => nomatch h
  | _ +> row, _ => row

def tail : Trace F S → Trace F S
  | <+>  => <+>
  | rest +> _ => rest

lemma tail_len : (trace : Trace F S) → trace.tail.len = trace.len - 1
  | <+>  => rfl
  | rest +> _ => by rw [tail, len, Nat.succ_sub_one]

@[table_norm]
def forAllRowsOfTraceWithIndex
    (trace : Trace F S) (prop : Row F S → ℕ → Prop) : Prop :=
  inner trace prop
  where
  @[table_norm]
  inner : Trace F S → (Row F S → ℕ → Prop) → Prop
    | <+>, _ => true
    | rest +> row, prop => (prop row rest.len) ∧ inner rest prop

/-- variant where the condition receives the entire previous trace instead of just the length -/
def forAllRowsWithPrevious  : Trace F S → (Row F S → Trace F S → Prop) → Prop
  | <+>, _ => true
  | rest +> row, prop => (prop row rest) ∧ forAllRowsWithPrevious rest prop

def toList : Trace F S → List (Row F S)
  | <+> => []
  | rest +> row => rest.toList.concat row

lemma toList_length : (trace : Trace F S) → trace.toList.length = trace.len
  | <+> => rfl
  | rest +> _ => by
    rw [toList, List.length_concat, len, Nat.succ_inj]
    exact rest.toList_length

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

@[table_norm]
def lastRow {M : ℕ+} (trace : TraceOfLength F S M) : S F :=
  trace.val.lastRow (by rw [trace.property]; exact M.pos)

def tail {M : ℕ} (trace : TraceOfLength F S M) : TraceOfLength F S (M - 1) :=
  ⟨ trace.val.tail, by rw [trace.val.tail_len, trace.prop] ⟩

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
  trace.val.forAllRowsOfTraceWithIndex prop

def forAllRowsWithPrevious {N : ℕ}
    (trace : TraceOfLength F S N) (prop : Row F S → (i : ℕ) → TraceOfLength F S i → Prop) : Prop :=
  trace.val.forAllRowsWithPrevious fun row rest => prop row rest.len ⟨ rest, rfl ⟩

def toList {N : ℕ} (trace : TraceOfLength F S N) : List.Vector (Row F S) N :=
  ⟨ trace.val.toList, by rw [trace.val.toList_length, trace.prop] ⟩

def take : {N : ℕ} → TraceOfLength F S N → (i : Fin (N + 1)) → TraceOfLength F S i
  | 0, ⟨ <+>, h0 ⟩, i => ⟨ <+>, i.val_eq_zero.symm ▸ rfl ⟩
  | N + 1, ⟨ rest +> row, h ⟩, ⟨ i, hi ⟩ =>
    if hi' : i = N + 1 then
      -- if `i` is the full length, we return the whole trace
      ⟨ rest +> row, hi' ▸ h ⟩
    else
      take ⟨ rest, Nat.succ_inj.mp h ⟩ ⟨ i, by omega ⟩

end TraceOfLength
variable {W: ℕ+} {α: Type}

/--
  A cell offset is an offset in a table that points to a specific cell in a row.
  It is used to define a relative position in the trace.
  `W` is the size of the "vertical window", which means that we can reference at most
  `W` rows above the current row.
  To make sure that the vertical offset is bounded, it is represented as a `Fin W`.
-/
structure CellOffset (W: ℕ+) (S : Type → Type) [ProvableType S]  where
  row: Fin W
  column: Fin (size S)

instance : Repr (CellOffset W S) where
  reprPrec off _ := "⟨" ++ reprStr off.row ++ ", " ++ reprStr off.column ++ "⟩"

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

instance : Repr (Cell W S) where
  reprPrec cell _ := match cell with
    | .input off => ".input " ++ reprStr off
    | .aux i => ".aux " ++ reprStr i

/--
Mapping between cell offsets in the table and variable indices.

The mapping must maintain the invariant that each variable is assigned to at most one cell.
On the other hand, a cell can be assigned zero, one or more variables.
-/
structure CellAssignment (W: ℕ+) (S : Type → Type) [ProvableType S] where
  offset : ℕ -- number of variables
  aux_length : ℕ -- maximum number of auxiliary cells (i.e. those not part of the input/output layout)

  /-- every variable is assigned to exactly one cell in the trace -/
  vars : Vector (Cell W S) offset

namespace CellAssignment
instance : Repr (CellAssignment W S) where
  reprPrec := fun { offset, aux_length, vars } _ =>
    "{ offset := " ++ reprStr offset ++ ", aux_length := " ++ reprStr aux_length ++ ", vars := " ++ reprStr vars ++ "}"

@[table_assignment_norm, reducible]
def empty (W: ℕ+) : CellAssignment W S where
  offset := 0
  aux_length := 0
  vars := #v[]

@[table_assignment_norm]
def push_var_aux (assignment: CellAssignment W S) : CellAssignment W S where
  offset := assignment.offset + 1
  aux_length := assignment.aux_length + 1
  vars := assignment.vars.push (.aux assignment.aux_length)

@[table_assignment_norm]
def push_vars_aux (assignment: CellAssignment W S) (n : ℕ) : CellAssignment W S where
  offset := assignment.offset + n
  aux_length := assignment.aux_length + n
  vars := assignment.vars ++ (.mapRange n fun i => .aux (assignment.aux_length + i) : Vector (Cell W S) n)

@[table_assignment_norm]
def push_var_input (assignment: CellAssignment W S) (off: CellOffset W S) : CellAssignment W S where
  offset := assignment.offset + 1
  aux_length := assignment.aux_length
  vars := assignment.vars.push (.input off)

@[table_assignment_norm]
def push_row (assignment: CellAssignment W S) (row: Fin W) : CellAssignment W S :=
  let row_vars : Vector (Cell W S) (size S) := .mapFinRange _ fun col => .input ⟨ row, col ⟩
  {
    offset := assignment.offset + size S
    aux_length := assignment.aux_length
    vars := assignment.vars ++ row_vars
  }

@[table_assignment_norm]
def set_var_input (assignment: CellAssignment W S) (off: CellOffset W S) (var: ℕ) : CellAssignment W S :=
  let vars := assignment.vars.set? var (.input off)
  -- note that we don't change the `aux_length` and the indices of existing aux variables.
  -- that would unnecessarily complicate reasoning about the assignment
  { assignment with vars }

/--
  The number of auxiliary cells in the final assignment
-/
def num_aux (assignment: CellAssignment W S) : ℕ :=
  assignment.vars.foldl (fun acc cell =>
    match cell with
    | .input _ => acc
    | .aux _ => acc + 1
  ) 0

end CellAssignment

/--
  Context of the TableConstraint that keeps track of the current state, this includes the underlying
  offset, and the current assignment of the variables to the cells in the trace.
-/
structure TableContext (W: ℕ+) (S : Type → Type) (F : Type) [Field F] [ProvableType S] where
  circuit : Operations F
  assignment : CellAssignment W S
deriving Repr

variable [Field F] {α : Type}

namespace TableContext
@[reducible, table_norm, table_assignment_norm]
def empty : TableContext W S F where
  circuit := []
  assignment := .empty W

@[reducible, table_norm, table_assignment_norm]
def offset (table : TableContext W S F) : ℕ := table.circuit.local_length
end TableContext

@[reducible, table_norm, table_assignment_norm]
def TableConstraint (W: ℕ+) (S : Type → Type) (F : Type) [Field F] [ProvableType S] :=
  StateM (TableContext W S F)

@[table_norm, table_assignment_norm]
theorem bind_def {β : Type} (f : TableConstraint W S F α) (g : α → TableConstraint W S F β) :
  (f >>= g) = fun ctx =>
    let (a, ctx') := f ctx
    g a ctx' := rfl

instance [Repr F] : Repr (TableConstraint W S F α) where
  reprPrec table _ := reprStr (table .empty).2

@[table_assignment_norm]
def assignment_from_circuit (as: CellAssignment W S) : Operations F → CellAssignment W S
  | [] => as
  | .witness m _ :: ops => assignment_from_circuit (as.push_vars_aux m) ops
  | .assert _ :: ops => assignment_from_circuit as ops
  | .lookup _ :: ops => assignment_from_circuit as ops
  | .subcircuit s :: ops => assignment_from_circuit (as.push_vars_aux s.local_length) ops

-- alternative, simpler definition, but makes it harder for lean to check defeq `(window_env ..).get i = ..`
def assignment_from_circuit' (as: CellAssignment W S) (ops : Operations F) : CellAssignment W S where
  offset := as.offset + ops.local_length
  aux_length := as.aux_length + ops.local_length
  vars := as.vars ++ (.mapRange _ fun i => .aux (as.aux_length + i) : Vector (Cell W S) _)

/--
A `MonadLift` instance from `Circuit` to `TableConstraint` means that we can just use
all circuit operations inside a table constraint.
-/
@[reducible, table_norm, table_assignment_norm]
instance : MonadLift (Circuit F) (TableConstraint W S F) where
  monadLift circuit ctx :=
    let (a, ops) := circuit ctx.circuit.local_length
    (a, {
      circuit := ctx.circuit ++ ops,
      assignment := assignment_from_circuit ctx.assignment ops
    })

namespace TableConstraint
@[reducible, table_norm, table_assignment_norm]
def final_offset (table : TableConstraint W S F α) : ℕ :=
  table .empty |>.snd.circuit.local_length

@[table_norm]
def operations (table : TableConstraint W S F α) : Operations F :=
  table .empty |>.snd.circuit

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
  let assignment := table.final_assignment
  .mk fun i =>
    if hi : i < assignment.offset then
      match assignment.vars[i] with
      | .input ⟨i, j⟩ => window.get i j
      | .aux k => aux_env.get k
    else aux_env.get (i + assignment.aux_length)

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
def output {α: Type} (table : TableConstraint W S F α) : α :=
  table .empty |>.fst

/--
  Get a fresh variable for each cell in a given row
-/
@[table_norm, table_assignment_norm]
def get_row (row : Fin W) : TableConstraint W S F (Var S F) :=
  modifyGet fun ctx =>
    let ctx' : TableContext W S F := {
      circuit := ctx.circuit ++ [.witness (size S) fun env => .mapRange _ fun i => env.get (ctx.offset + i)],
      assignment := ctx.assignment.push_row row
    }
    (var_from_offset S ctx.offset, ctx')

/--
  Get a fresh variable for each cell in the current row
-/
@[table_norm, table_assignment_norm]
def get_curr_row : TableConstraint W S F (Var S F) := get_row 0

/--
  Get a fresh variable for each cell in the next row
-/
@[table_norm, table_assignment_norm]
def get_next_row : TableConstraint W S F (Var S F) := get_row 1

@[table_norm, table_assignment_norm]
def assign_var (off : CellOffset W S) (v : Variable F) : TableConstraint W S F Unit :=
  modify fun ctx =>
    let assignment := ctx.assignment.set_var_input off v.index
    { ctx with assignment }

@[table_norm, table_assignment_norm]
def assign (off : CellOffset W S) : Expression F → TableConstraint W S F Unit
  -- a variable is assigned directly
  | .var v => assign_var off v
  -- a composed expression or constant is first stored in a new variable, which is assigned
  | x => do
    let new_var ← witness_var x.eval
    assert_zero (x - var new_var)
    assign_var off new_var

@[table_norm, table_assignment_norm]
def assign_curr_row {W: ℕ+} (curr : Var S F) : TableConstraint W S F Unit :=
  let vars := to_vars curr
  forM (List.finRange (size S)) fun i =>
    assign (.curr i) (vars.get i)

@[table_norm, table_assignment_norm]
def assign_next_row {W: ℕ+} (next : Var S F) : TableConstraint W S F Unit :=
  let vars := to_vars next
  forM (List.finRange (size S)) fun i =>
    assign (.next i) (vars.get i)
end TableConstraint

export TableConstraint (window_env get_curr_row get_next_row assign_var assign assign_next_row assign_curr_row)

@[reducible]
def SingleRowConstraint (S : Type → Type) (F : Type) [Field F] [ProvableType S] := TableConstraint 1 S F Unit

@[reducible]
def TwoRowsConstraint (S : Type → Type) (F : Type) [Field F] [ProvableType S] := TableConstraint 2 S F Unit

-- specify a row, either counting from the start or from the end of the trace.
inductive RowIndex where
  | fromStart : ℕ → RowIndex
  | fromEnd : ℕ → RowIndex

inductive TableOperation (S : Type → Type) (F : Type) [Field F] [ProvableType S] where
  /--
    A `Boundary` constraint is a constraint that is applied only to a specific row
  -/
  | Boundary: RowIndex → SingleRowConstraint S F → TableOperation S F

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

instance : Repr RowIndex where
  reprPrec
    | .fromStart i, _ => reprStr (i : ℤ)
    | .fromEnd i, _ => reprStr (-i-1 : ℤ)

instance [Repr F] : Repr (TableOperation S F) where
  reprPrec op _ := match op with
    | .Boundary i c => "Boundary " ++ reprStr i ++ " " ++ reprStr c
    | .EveryRow c => "EveryRow " ++ reprStr c
    | .EveryRowExceptLast c => "EveryRowExceptLast " ++ reprStr c

export TableOperation (Boundary EveryRow EveryRowExceptLast)

/--
  The constraints hold over a trace if the hold individually in a suitable environment, where the
  environment is derived from the `CellAssignment` functions. Intuitively, if a variable `x`
  is assigned to a field element in the trace `y: F` using a `CellAssignment` function, then ` env x = y`
-/
@[table_norm]
def table_constraints_hold {N : ℕ} (constraints : List (TableOperation S F))
  (trace: TraceOfLength F S N) (env: ℕ → ℕ → Environment F) : Prop :=
  let constraints_and_envs := constraints.mapIdx (fun i cs => (cs, env i))
  foldl N constraints_and_envs trace.val constraints_and_envs
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
  foldl (N : ℕ) (cs : List (TableOperation S F × (ℕ → (Environment F)))) :
    Trace F S → (cs_iterator: List (TableOperation S F × (ℕ → (Environment F)))) → Prop
    -- if the trace has at least two rows and the constraint is a "every row except last" constraint, we apply the constraint
    | trace +> curr +> next, (⟨.EveryRowExceptLast constraint, env⟩)::rest =>
        let others := foldl N cs (trace +> curr +> next) rest
        let window : TraceOfLength F S 2 := ⟨<+> +> curr +> next, rfl ⟩
        constraint.constraints_hold_on_window window (env (trace.len + 1)) ∧ others

    -- if the trace has at least one row and the constraint is a boundary constraint, we apply the constraint if the
    -- index is the same as the length of the remaining trace
    | trace +> row, (⟨.Boundary idx constraint, env⟩)::rest =>
        let others := foldl N cs (trace +> row) rest
        let window : TraceOfLength F S 1 := ⟨<+> +> row, rfl⟩
        let targetIdx := match idx with
          | .fromStart i => i
          | .fromEnd i => N - 1 - i
        (if trace.len = targetIdx then constraint.constraints_hold_on_window window (env trace.len) else True) ∧ others

    -- if the trace has at least one row and the constraint is a "every row" constraint, we apply the constraint
    | trace +> row, (⟨.EveryRow constraint, env⟩)::rest =>
        let others := foldl N cs (trace +> row) rest
        let window : TraceOfLength F S 1 := ⟨<+> +> row, rfl⟩
        constraint.constraints_hold_on_window window (env trace.len) ∧ others

    -- if the trace has not enough rows for the "every row except last" constraint, we skip the constraint
    | trace, (⟨.EveryRowExceptLast _, _⟩)::rest =>
        foldl N cs trace rest

    -- if the cs_iterator is empty, we start again with the initial constraints on the next row
    | trace +> _, [] =>
        foldl N cs trace cs

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
    := by repeat constructor

def FormalTable.statement (table : FormalTable F S) (N : ℕ) (trace: TraceOfLength F S N) : Prop :=
  table.assumption N → table.spec trace

-- add some important lemmas to simp sets
attribute [table_norm] List.mapIdx List.mapIdx.go
attribute [table_norm low] size from_elements to_elements to_vars from_vars
attribute [table_assignment_norm low] to_elements
attribute [table_norm] Circuit.constraints_hold.soundness

attribute [table_norm, table_assignment_norm] Vector.set? List.set_cons_succ List.set_cons_zero

attribute [table_norm, table_assignment_norm] liftM monadLift
attribute [table_norm, table_assignment_norm] StateT.bind
attribute [table_norm, table_assignment_norm] modify modifyGet MonadStateOf.modifyGet StateT.modifyGet

-- simp lemma to simplify updated circuit after an assignment
@[table_norm, table_assignment_norm]
theorem TableConstraint.assign_var_circuit : ∀ ctx (off : CellOffset W S) (v : Variable F),
  (assign_var off v ctx).snd.circuit = ctx.circuit := by intros; rfl

/--
Tactic script to unfold `assign_curr_row` and `assign_next_row` in a `TableConstraint`.

TODO this is fairly useless without support for `at h` syntax
-/
syntax "simp_assign_row" : tactic
macro_rules
  | `(tactic|simp_assign_row) =>
    `(tactic|(
    simp only [assign_curr_row, assign_next_row, size]
    rw [List.finRange, List.ofFn]
    repeat rw [Fin.foldr_succ]
    rw [Fin.foldr_zero]
    repeat rw [List.forM_cons]
    rw [List.forM_nil, bind_pure_unit]
    simp only [seval, to_vars, to_elements, Vector.get, Fin.cast_eq_self, Fin.val_zero, Fin.val_one, Fin.isValue,
      List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ, Fin.succ_zero_eq_one]))
