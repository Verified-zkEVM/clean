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
def Row (F : Type) (S : Type -> Type) [StructuredElements S] := S F

@[table_norm]
def Row.get {F : Type} {S : Type -> Type} [struct: StructuredElements S] (row : Row F S) (i : Fin struct.size) : F :=
  let elems := StructuredElements.to_elements row
  elems.get i

/--
  A trace is an inductive list of rows. It can be viewed as a structured
  environment that maps cells to field elements.
-/
inductive Trace (F : Type) (S : Type -> Type) [StructuredElements S] :=
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
def len {F : Type} {S : Type -> Type} [StructuredElements S] : Trace F S -> ℕ
  | <+> => 0
  | rest +> _ => Nat.succ rest.len

/--
  Induction principle that applies for every row in the trace, where the inductive step takes into
  account the previous two rows.
-/
def everyRowTwoRowsInduction {F : Type}
    {S : Type -> Type} [StructuredElements S] {P : Trace F S → Sort*}
    (zero : P (<+>))
    (one : ∀ row : Row F S, P (empty +> row))
    (more : ∀ curr next : Row F S,
      ∀ rest : Trace F S, P (rest) -> P (rest +> curr) → P (rest +> curr +> next))
    : ∀ trace, P trace
  | <+> => zero
  | <+> +> first => one first
  | rest +> curr +> _ => more _ _ _
    (everyRowTwoRowsInduction zero one more (rest))
    (everyRowTwoRowsInduction zero one more (rest +> curr))

lemma len_le_succ {F : Type}
    {S : Type -> Type} [StructuredElements S]
    (trace : Trace F S) (row : Row F S) : trace.len ≤ (trace +> row).len :=
  match trace with
  | <+> => by simp only [len, Nat.succ_eq_add_one, zero_add, zero_le]
  | (rest +> _) =>
    by simp only [len, Nat.succ_eq_add_one, le_add_iff_nonneg_right, zero_le]

lemma len_ge_succ_of_ge {N : ℕ} {F : Type}
    {S : Type -> Type} [StructuredElements S]
    (trace : Trace F S) (row : Row F S) (_h : trace.len ≥ N) : (trace +> row).len ≥ N :=
  match trace with
  | <+> => by
      simp only [len, ge_iff_le, nonpos_iff_eq_zero, Nat.succ_eq_add_one, zero_add] at *
      simp only [_h, zero_le]
  | (rest +> row) => by simp only [len, Nat.succ_eq_add_one, ge_iff_le] at *; linarith

/--
  This induction principle states that if a trace length is at leas two, then to prove a property
  about the whole trace, we can provide just a proof for the first two rows, and then a proof
  for the inductive step.
-/
def everyRowTwoRowsInduction' {F : Type}
      {S : Type -> Type} [StructuredElements S]
      {P : (t : Trace F S) → t.len ≥ 2 → Sort*}
    (base : ∀ first second (h : (<+> +> first +> second).len ≥ 2), P (<+> +> first +> second) h)
    (more : ∀ curr next : Row F S,
      ∀ (rest : Trace F S) (h : rest.len ≥ 2),
        P rest h ->
        P (rest +> curr) (len_ge_succ_of_ge _ _ h) →
        P (rest +> curr +> next) (len_ge_succ_of_ge _ _ (len_ge_succ_of_ge _ _ h)))
    : ∀ (trace : Trace F S) (h : trace.len ≥ 2), P trace h
  -- the cases where the trace is empty or has only one row are trivial,
  -- since the length is greater than 2
  | <+> => by intro h; contradiction
  | <+> +> first => by intro h; contradiction
  | <+> +> first +> second => fun h => base first second h
  | rest +> curr +> next =>
      let ih' := (everyRowTwoRowsInduction' base more (rest))
      let ih'' := (everyRowTwoRowsInduction' base more (rest +> curr))
      (Nat.lt_or_ge 2 rest.len).by_cases
        -- TODO: this definition should be similar to Nat.letRec
        (by sorry)
        (by sorry)

/--
  Get the row at a specific index in the trace, starting from the bottom of the trace
-/
@[table_norm]
def getLeFromBottom {F : Type}
    {S : Type -> Type} [struct: StructuredElements S]:
    (trace : Trace F S) -> (row : Fin trace.len) -> (col : Fin struct.size) -> F
  | _ +> currRow, ⟨0, _⟩, j => currRow.get j
  | rest +> _, ⟨i + 1, h⟩, j => getLeFromBottom rest ⟨i, Nat.le_of_succ_le_succ h⟩ j

end Trace


/--
  A trace of length N is a trace with exactly N rows.
-/
def TraceOfLength (F : Type) (S : Type -> Type) [StructuredElements S] (N : ℕ) : Type :=
  { env : Trace F S // env.len = N }

namespace TraceOfLength

/--
  Get the row at a specific index in the trace, starting from the top
-/
@[table_norm]
def get {N: ℕ+} {M : ℕ} {F : Type}
    {S : Type -> Type} [StructuredElements S]:
    (env : TraceOfLength F S M) -> (i : Fin M) -> (j : Fin N) -> F
  | ⟨env, h⟩, i, j => env.getLeFromBottom ⟨
      M - 1 - i,
      by rw [h]; apply Nat.sub_one_sub_lt_of_lt; exact i.is_lt
    ⟩ j

/--
  Apply a proposition to every row in the trace
-/
@[table_norm]
def forAllRowsOfTrace {N : ℕ} {F : Type}
    {S : Type -> Type} [StructuredElements S]
    (trace : TraceOfLength F S N) (prop : Row F S -> Prop) : Prop :=
  inner trace.val prop
  where
  @[table_norm]
  inner : Trace F S -> (Row F S -> Prop) -> Prop
    | <+>, _ => true
    | rest +> row, prop => prop row ∧ inner rest prop

/--
  Apply a proposition to every row in the trace except the last one
-/
@[table_norm]
def forAllRowsOfTraceExceptLast {N : ℕ} {F : Type}
    {S : Type -> Type} [StructuredElements S]
    (trace : TraceOfLength F S N) (prop : Row F S -> Prop) : Prop :=
  inner trace.val prop
  where
  inner : Trace F S -> (Row F S -> Prop) -> Prop
    | <+>, _ => true
    | <+> +> _, _ => true
    | rest +> curr +> _, prop => prop curr ∧ inner (rest +> curr) prop


/--
  Apply a proposition, which could be dependent on the row index, to every row of the trace
-/
@[table_norm]
def forAllRowsOfTraceWithIndex {N : ℕ} {F : Type}
    {S : Type -> Type} [StructuredElements S]
    (trace : TraceOfLength F S N) (prop : Row F S -> ℕ -> Prop) : Prop :=
  inner trace.val prop
  where
  @[table_norm]
  inner : Trace F S -> (Row F S -> ℕ -> Prop) -> Prop
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
structure CellOffset (W: ℕ+) (S : Type -> Type) [struct: StructuredElements S]  where
  rowOffset: Fin W
  column: Fin (struct.size)
deriving Repr

namespace CellOffset

/--
  Current row offset
-/
@[table_norm]
def curr {W : ℕ+} {S : Type -> Type} [struct: StructuredElements S] (j : Fin (struct.size)) :  CellOffset W S := ⟨0, j⟩

/--
  Next row offset
-/
@[table_norm]
def next {W : ℕ+} {S : Type -> Type} [struct: StructuredElements S] (j : Fin (struct.size)) :  CellOffset W S := ⟨1, j⟩

end CellOffset

/--
  Mapping from the index of a variable to a cell offset in the table.
-/
@[reducible]
def CellAssignment (W: ℕ+) (S : Type -> Type) [StructuredElements S] := ℕ -> CellOffset W S

/--
  Atomic operations for constructing a table constraint, which is a constraint applied to a window
  of rows in a table.
-/
inductive TableConstraintOperation (W : ℕ+) (S : Type -> Type) (F : Type) [Field F] [struct: StructuredElements S] where
  /--
    Add some witnessed variable to the context
  -/
  | Witness : CellOffset W S -> (compute : Unit → F) -> TableConstraintOperation W S F

  /--
    Witness a fresh variable for each cell in the row at some offset `off` in the trace
  -/
  | GetRow : (off : Fin W) -> TableConstraintOperation W S F

  /--
    Allocate a subcircuit in the trace
  -/
  | Allocate: {n: ℕ} → SubCircuit F n -> TableConstraintOperation W S F

  /--
    Assign a variable to a cell in the trace
  -/
  | Assign : Variable F -> CellOffset W S -> TableConstraintOperation W S F

/--
  Context of the TableConstraint that keeps track of the current state, this includes the underlying
  offset, and the current assignment of the variables to the cells in the trace.
-/
structure TableContext (W: ℕ+) (S : Type -> Type)  (F : Type) [Field F] [struct: StructuredElements S] where
  offset: ℕ
  assignment : CellAssignment W S

/--
  An empty context has offset zero, and all variables are assigned by default to the first cell
-/
@[reducible]
def TableContext.empty {W: ℕ+} {S : Type -> Type}  {F : Type} [Field F] [StructuredElements S] : TableContext W S F := ⟨
  0,
  -- TODO: is there a better way?
  fun _ => ⟨0, 0⟩
⟩

namespace TableConstraintOperation

/--
  Returns the updated table context after applying the table operation
-/
@[table_norm]
def update_context {W: ℕ+} {S : Type -> Type}  {F : Type} [Field F] [struct: StructuredElements S] (ctx: TableContext W S F) :
    TableConstraintOperation W S F → TableContext W S F
  /-
    Witnessing a fresh variable for a table offets just increments the offset and add the mapping
    from the variable index to the cell offset in the assignment mapping
  -/
  | Witness offset _ => {
      offset := ctx.offset + 1,
      assignment := fun x => if x = ctx.offset then offset else ctx.assignment x
    }

  /-
    Getting a row is equivalent to witnessing a fresh variable for each cell in the row
  -/
  | GetRow off => {
      offset := ctx.offset + struct.size,
      assignment := fun x => if x >= ctx.offset && x < ctx.offset+struct.size then ⟨off, x-ctx.offset⟩ else ctx.assignment x
    }

  /-
    Allocation of a sub-circuit moves the context offset by the witness length of the sub-circuit
  -/
  | Allocate { ops, .. } => {
      offset := ctx.offset + FlatOperation.witness_length ops,
      assignment := ctx.assignment
    }

  /-
    Assigning a variable to a cell in the trace just updates the assignment mapping
  -/
  | Assign v offset => {
      offset := ctx.offset,
      assignment := fun x => if x = v.index then offset else ctx.assignment x
    }

instance {W: ℕ+} {S : Type -> Type}  {F : Type} [Field F] [StructuredElements S] [Repr F] :
    ToString (TableConstraintOperation W S F) where
  toString
    | Witness offset _ => "(Witness " ++ reprStr offset ++ ")"
    | GetRow off => "(GetRow " ++ reprStr off ++ ")"
    | Allocate {ops, ..} => "(Allocate " ++ reprStr ops ++ ")"
    | Assign v offset => "(Assign " ++ reprStr v ++ " " ++ reprStr offset ++ ")"

end TableConstraintOperation


@[table_norm]
def TableConstraint (W: ℕ+) (S : Type -> Type)  (F : Type) [Field F] [StructuredElements S] (α : Type) :=
  TableContext W S F → (TableContext W S F × List (TableConstraintOperation W S F)) × α

namespace TableConstraint
instance (W: ℕ+) (S : Type -> Type)  (F : Type) [Field F] [StructuredElements S] : Monad (TableConstraint W S F) where
  pure a ctx := ((ctx, []), a)
  bind f g ctx :=
    let ((ctx', ops), a) := f ctx
    let ((ctx'', ops'), b) := g a ctx'
    ((ctx'', ops ++ ops'), b)

@[table_norm]
def as_table_operation {α: Type} {W: ℕ+} {S : Type -> Type} {F : Type} [Field F] [StructuredElements S]
  (f : TableContext W S F -> TableConstraintOperation W S F × α) : TableConstraint W S F α :=
  fun ctx =>
  let (op, a) := f ctx
  let ctx' := TableConstraintOperation.update_context ctx op
  ((ctx', [op]), a)

def operations {α: Type} {W: ℕ+} {S : Type -> Type} {F : Type} [Field F] [StructuredElements S] (table : TableConstraint W S F α):
    List (TableConstraintOperation W S F) :=
  let ((_, ops), _) := table TableContext.empty
  ops

def assignment {α: Type} {W: ℕ+} {S : Type -> Type} {F : Type} [Field F] [StructuredElements S] (table : TableConstraint W S F α):
    CellAssignment W S :=
  let ((ctx, _), _) := table TableContext.empty
  ctx.assignment

/--
  A table constraint holds on a window of rows if the constraints hold on a suitable environment.
  In particular, we construct the environment by taking directly the result of the assignment function
  so that every variable evaluate to the trace cell value which is assigned to
-/
@[table_norm]
def constraints_hold_on_window {F : Type} {W : ℕ+} [Field F]
    {S : Type -> Type} [StructuredElements S]
    (table : TableConstraint W S F Unit) (window: TraceOfLength F S W) : Prop :=
  let ((ctx, ops), ()) := table TableContext.empty

  -- construct an env by simply taking the result of the assignment function
  let env : Environment F := ⟨ fun x =>
    match ctx.assignment x with
    | ⟨i, j⟩ => window.get i j
  ⟩

  -- then we fold over allocated sub-circuits
  -- lifting directly to the soundness of the sub-circuit
  foldl ops env
  where
  @[table_norm]
  foldl : List (TableConstraintOperation W S F) -> (env: Environment F) -> Prop
  | [], _ => true
  | op :: ops, env =>
    match op with
    | TableConstraintOperation.Allocate {soundness ..} => soundness env ∧ foldl ops env
    | _ => foldl ops env

def output {α: Type} {W: ℕ+} {S : Type -> Type}  {F : Type} [Field F] [StructuredElements S] (table : TableConstraint W S F α) : α :=
  let ((_, _), a) := table TableContext.empty
  a

def witness_cell {W: ℕ+} {S : Type -> Type}  {F : Type} [Field F] [StructuredElements S]
    (off : CellOffset W S) (compute : Unit → F): TableConstraint W S F (Variable F) :=
  as_table_operation fun ctx =>
  (TableConstraintOperation.Witness off compute, ⟨ ctx.offset ⟩)

def get_cell {W: ℕ+} {S : Type -> Type}  {F : Type} [Field F] [StructuredElements S]
    (off : CellOffset W S): TableConstraint W S F (Variable F) :=
  as_table_operation fun ctx =>
  (TableConstraintOperation.Witness off (fun _ => 0), ⟨ ctx.offset ⟩)

/--
  Get a fresh variable for each cell in the current row
-/
@[table_norm]
def get_curr_row {W: ℕ+} {S : Type -> Type} {F : Type} [Field F] [struct: StructuredElements S] :
    TableConstraint W S F (Vector (Expression F) struct.size) :=
  as_table_operation fun ctx =>
  let vars := Vector.init (fun i => ⟨ctx.offset + i⟩)
  let exprs := vars.map (fun v => Expression.var v)
  (TableConstraintOperation.GetRow 0, exprs)

/--
  Get a fresh variable for each cell in the next row
-/
@[table_norm]
def get_next_row {W: ℕ+} {S : Type -> Type} {F : Type} [Field F] [struct: StructuredElements S] :
    TableConstraint W S F (Vector (Expression F) struct.size) :=
  as_table_operation fun ctx =>
  let vars := Vector.init (fun i => ⟨ctx.offset + i⟩)
  let exprs := vars.map (fun v => Expression.var v)
  (TableConstraintOperation.GetRow 1, exprs)

def subcircuit
    {W: ℕ+} {S : Type -> Type} {F : Type} [Field F] [StructuredElements S]
    {α β : TypePair} [ProvableType β] [ProvableType α]
    (circuit: FormalCircuit F β α) (b: β.var F) : TableConstraint W S F (α.var F) :=
  as_table_operation fun ctx =>
  let ⟨ a, subcircuit ⟩ := Circuit.formal_circuit_to_subcircuit ctx.offset circuit b
  (TableConstraintOperation.Allocate subcircuit, a)

def assertion
    {W: ℕ+} {S : Type -> Type} {F : Type} [Field F] [StructuredElements S]
    {β : TypePair} [ProvableType β]
    (circuit: FormalAssertion F β) (b: β.var F) : TableConstraint W S F Unit :=
  as_table_operation fun ctx =>
    let subcircuit := Circuit.formal_assertion_to_subcircuit ctx.offset circuit b
    (TableConstraintOperation.Allocate subcircuit, ())

def assign {W: ℕ+} {S : Type -> Type} {F : Type} [Field F] [StructuredElements S]
    (v: Variable F) (off : CellOffset W S) : TableConstraint W S F Unit :=
  as_table_operation fun _ =>
  (TableConstraintOperation.Assign v off, ())

end TableConstraint


@[reducible]
def SingleRowConstraint (S : Type -> Type) (F : Type) [Field F] [StructuredElements S] := TableConstraint 1 S F Unit

@[reducible]
def TwoRowsConstraint (S : Type -> Type) (F : Type) [Field F] [StructuredElements S] := TableConstraint 2 S F Unit

inductive TableOperation (S : Type -> Type) (F : Type) [Field F] [StructuredElements S] where
  /--
    A `Boundary` constraint is a constraint that is applied only to a specific row
  -/
  | Boundary: ℕ -> SingleRowConstraint S F -> TableOperation S F

  /--
    An `EveryRow` constraint is a constraint that is applied to every row.
    It can only reference cells on the same row
  -/
  | EveryRow: SingleRowConstraint S F -> TableOperation S F

  /--
    An `EveryRowExceptLast` constraint is a constraint that is applied to every row except the last.
    It can reference cells from the current row, or the next row
  -/
  | EveryRowExceptLast: TwoRowsConstraint S F -> TableOperation S F


/--
  The constraints hold over a trace if the hold individually in a suitable environment, where the
  environment is derived from the `CellAssignment` functions. Intuitively, if a variable `x`
  is assigned to a field element in the trace `y: F` using a `CellAssignment` function, then ` env x = y`
-/
@[table_norm]
def table_constraints_hold {N : ℕ}
    {S : Type -> Type}  {F : Type} [Field F] [StructuredElements S]
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
  foldl (cs : List (TableOperation S F)) : Trace F S -> (cs_iterator: List (TableOperation S F)) -> Prop
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
    -- TODO: this is fine if the trace length M is >= 2, but we should check this somehow
    | trace, (TableOperation.EveryRowExceptLast _)::rest =>
        foldl cs trace rest

    -- if the cs_iterator is empty, we start again with the initial constraints on the next row
    | trace +> _, [] =>
        foldl cs trace cs

    -- if the trace is empty, we are done
    | <+>, _ => True


structure FormalTable (F : Type) [Field F] (S : Type -> Type) [struct: StructuredElements S] where
  -- list of constraints that are applied over the table
  constraints : List (TableOperation S F)

  -- assumptions for the table
  assumptions {N : ℕ} : TraceOfLength F S N -> Prop

  -- specification for the table
  spec {N : ℕ} : TraceOfLength F S N -> Prop

  -- the soundness states that if the assumptions hold, then
  -- the constraints hold implies that the spec holds
  soundness :
    ∀ (N : ℕ) (trace: TraceOfLength F S N),
    assumptions trace ->
    table_constraints_hold constraints trace ->
    spec trace
