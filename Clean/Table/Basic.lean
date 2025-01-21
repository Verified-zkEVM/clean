import Mathlib.Algebra.Field.Basic
import Mathlib.Data.ZMod.Basic
import Clean.Utils.Primes
import Clean.Utils.Vector
import Clean.Circuit.Basic
import Clean.Circuit.SubCircuit
import Clean.Circuit.Expression
import Clean.Circuit.Provable
import Clean.Utils.Field

/--
  A row is an instance of a structured elements structure, which has exactly size M.
-/
structure Row (M : ℕ+) (F : Type) (S : Type -> Type) [StructuredElements S F] where
  elems : S F
  size_h : StructuredElements.size S F = M


def Row.get {M : ℕ+} {F : Type} {S : Type -> Type} [StructuredElements S F] (row : Row M F S) (i : Fin M) : F :=
  let elems := StructuredElements.to_elements row.elems
  by rw [row.size_h] at elems; exact elems.get i


/--
  A trace is an inductive list of rows. It can be viewed as a structured
  environment that maps cells to field elements.
-/
inductive Trace (M : ℕ+) (F : Type)  (S : Type -> Type) [StructuredElements S F] :=
  /-- An empty trace -/
  | empty : Trace M F S
  /-- Add a row to the end of the trace -/
  | cons (rest: Trace M F S) (row: Row M F S) : Trace M F S

@[inherit_doc] notation:67 "<+>" => Trace.empty
@[inherit_doc] infixl:67 " +> " => Trace.cons

namespace Trace
/--
  The length of a trace is the number of rows it contains.
-/
@[simp]
def len {M : ℕ+} {F : Type} {S : Type -> Type} [StructuredElements S F] : Trace M F S -> ℕ
  | <+> => 0
  | rest +> _ => Nat.succ rest.len

/--
  Induction principle that applies for every row in the trace, where the inductive step takes into
  acount the previous two rows.
-/
def everyRowTwoRowsInduction {M : ℕ+} {F : Type}
    {S : Type -> Type} [StructuredElements S F] {P : Trace M F S → Sort*}
    (zero : P (<+>))
    (one : ∀ row : Row M F S, P (empty +> row))
    (more : ∀ curr next : Row M F S,
      ∀ rest : Trace M F S, P (rest) -> P (rest +> curr) → P (rest +> curr +> next))
    : ∀ trace, P trace
  | <+> => zero
  | <+> +> first => one first
  | rest +> curr +> _ => more _ _ _
    (everyRowTwoRowsInduction zero one more (rest))
    (everyRowTwoRowsInduction zero one more (rest +> curr))

lemma len_le_succ {M : ℕ+} {F : Type}
    {S : Type -> Type} [StructuredElements S F]
    (trace : Trace M F S) (row : Row M F S) : trace.len ≤ (trace +> row).len :=
  match trace with
  | <+> => by simp [Trace.len]
  | (rest +> row) =>
    let ih := len_le_succ rest row
    by simp [Trace.len, ih, Nat.le_succ]

lemma len_ge_succ_of_ge {M : ℕ+} {N : ℕ} {F : Type}
    {S : Type -> Type} [StructuredElements S F]
    (trace : Trace M F S) (row : Row M F S) (_h : trace.len ≥ N) : (trace +> row).len ≥ N :=
  match trace with
  | <+> => by simp [Trace.len] at *; simp [_h]
  | (rest +> row) => by simp [Trace.len] at *; linarith

/--
  This induction principle states that if a trace length is at leas two, then to prove a property
  about the whole trace, we can provide just a proof for the first two rows, and then a proof
  for the inductive step.
-/
def everyRowTwoRowsInduction' {M : ℕ+} {F : Type}
      {S : Type -> Type} [StructuredElements S F]
      {P : (t : Trace M F S) → t.len ≥ 2 → Sort*}
    (base : ∀ first second (h : (<+> +> first +> second).len ≥ 2), P (<+> +> first +> second) h)
    (more : ∀ curr next : Row M F S,
      ∀ (rest : Trace M F S) (h : rest.len ≥ 2),
        P rest h ->
        P (rest +> curr) (len_ge_succ_of_ge _ _ h) →
        P (rest +> curr +> next) (len_ge_succ_of_ge _ _ (len_ge_succ_of_ge _ _ h)))
    : ∀ (trace : Trace M F S) (h : trace.len ≥ 2), P trace h
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

@[simp]
def getLeFromBottom {M :ℕ+} {F : Type}
      {S : Type -> Type} [StructuredElements S F]:
      (trace : Trace M F S) -> (row : Fin trace.len) -> (col : Fin M) -> F
  | _ +> currRow, ⟨0, _⟩, j => currRow.get j
  | rest +> _, ⟨i + 1, h⟩, j => getLeFromBottom rest ⟨i, Nat.le_of_succ_le_succ h⟩ j

end Trace


/--
  A trace of length M is a trace with exactly M rows.
-/
def TraceOfLength (F : Type) (S : Type -> Type) [StructuredElements S F]
  (M : ℕ+) (N : ℕ) : Type := { env : Trace M F S // env.len = N }

namespace TraceOfLength

@[simp]
def get {N: ℕ+} {M : ℕ} {F : Type}
    {S : Type -> Type} [StructuredElements S F]:
    (env : TraceOfLength F S N M) -> (i : Fin M) -> (j : Fin N) -> F
  | ⟨env, h⟩, i, j => env.getLeFromBottom ⟨
      M - 1 - i,
      by rw [h]; apply Nat.sub_one_sub_lt_of_lt; exact i.is_lt
    ⟩ j

/--
  Apply a proposition to every row in the trace
-/
@[simp]
def forAllRowsOfTrace {N: ℕ+} {M : ℕ} {F : Type}
    {S : Type -> Type} [StructuredElements S F]
    (trace : TraceOfLength F S N M) (prop : Row N F S -> Prop) : Prop :=
  inner trace.val prop
  where
  @[simp]
  inner : Trace N F S -> (Row N F S -> Prop) -> Prop
    | <+>, _ => true
    | rest +> row, prop => prop row ∧ inner rest prop

/--
  Apply a proposition to every row in the trace except the last one
-/
@[simp]
def forAllRowsOfTraceExceptLast {N: ℕ+} {M : ℕ} {F : Type}
    {S : Type -> Type} [StructuredElements S F]
    (trace : TraceOfLength F S N M) (prop : Row N F S -> Prop) : Prop :=
  inner trace.val prop
  where
  inner : Trace N F S -> (Row N F S -> Prop) -> Prop
    | <+>, _ => true
    | <+> +> _, _ => true
    | rest +> curr +> _, prop => prop curr ∧ inner (rest +> curr) prop


/--
  Apply a proposition, which could be dependent on the row index, to every row of the trace
-/
@[simp]
def forAllRowsOfTraceWithIndex {N: ℕ+} {M : ℕ} {F : Type}
    {S : Type -> Type} [StructuredElements S F]
    (trace : TraceOfLength F S N M) (prop : Row N F S -> ℕ -> Prop) : Prop :=
  inner trace.val prop
  where
  @[simp]
  inner : Trace N F S -> (Row N F S -> ℕ -> Prop) -> Prop
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
structure CellOffset (M W: ℕ+) where
  rowOffset: Fin W
  column: Fin M
deriving Repr

namespace CellOffset

def curr {M W : ℕ+} (j : Fin M) : CellOffset M W := ⟨0, j⟩
def next {M W: ℕ+} (j : Fin M) : CellOffset M W := ⟨1, j⟩

end CellOffset

/--
  Mapping from the index of a variable to a cell offset in the table.
-/
@[reducible]
def CellAssignment (M W: ℕ+) := ℕ -> CellOffset M W

/--
  Atomic operations for constructing a table constraint, which is a constraint applied to a window
  of rows in a table.
-/
inductive TableConstraintOperation (F : Type) [Field F] (M W : ℕ+) where
  /--
    Add some witnessed variable to the context
  -/
  | Witness : CellOffset M W -> (compute : Unit → F) -> TableConstraintOperation F M W

  /--
    Allocate a subcircuit in the trace
  -/
  | Allocate: SubCircuit F -> TableConstraintOperation F M W

  /--
    Assign a variable to a cell in the trace
  -/
  | Assign : Variable F -> CellOffset M W -> TableConstraintOperation F M W

/--
  Context of the TableConstraint that keeps track of the current state, this includes the underlying
  context of the gadgets, and the current assignment of the variables to the cells in the trace.
-/
structure TableContext (F : Type) (M W : ℕ+) where
  subContext: Context F
  assignment : CellAssignment M W

@[simp]
def TableContext.empty {F : Type} {M W : ℕ+} : TableContext F M W := ⟨
  Context.empty,
  -- TODO: is there a better way?
  fun _ => ⟨0, 0⟩
⟩

namespace TableConstraintOperation

@[simp]
def update_context {F : Type} {M W : ℕ+} [Field F] (ctx: TableContext F M W) : TableConstraintOperation F M W → TableContext F M W
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

instance {F : Type} {M W : ℕ+} [Field F] [Repr F] : ToString (TableConstraintOperation F M W) where
  toString
    | Witness offset _ => "(Witness " ++ reprStr offset ++ ")"
    | Allocate {ops, ..} => "(Allocate " ++ reprStr ops ++ ")"
    | Assign v offset => "(Assign " ++ reprStr v ++ " " ++ reprStr offset ++ ")"

end TableConstraintOperation


@[simp]
def TableConstraint (F : Type) [Field F] (M W : ℕ+) (α : Type) :=
  TableContext F M W → (TableContext F M W × List (TableConstraintOperation F M W)) × α

namespace TableConstraint
instance (F : Type) [Field F] (M W : ℕ+): Monad (TableConstraint F M W) where
  pure a ctx := ((ctx, []), a)
  bind f g ctx :=
    let ((ctx', ops), a) := f ctx
    let ((ctx'', ops'), b) := g a ctx'
    ((ctx'', ops ++ ops'), b)


def as_table_operation {α: Type} {F : Type} {M W : ℕ+} [Field F]
  (f : TableContext F M W -> TableConstraintOperation F M W × α) : TableConstraint F M W α :=
  fun ctx =>
  let (op, a) := f ctx
  let ctx' := TableConstraintOperation.update_context ctx op
  ((ctx', [op]), a)

def operations {α : Type} {F : Type} {M W : ℕ+} [Field F] (table : TableConstraint F M W α):
    List (TableConstraintOperation F M W) :=
  let ((_, ops), _) := table TableContext.empty
  ops

def assignment {α : Type} {F : Type} {M W : ℕ+} [Field F] (table : TableConstraint F M W α):
    CellAssignment M W :=
  let ((ctx, _), _) := table TableContext.empty
  ctx.assignment

/--
  A table constraint holds on a window of rows if the constraints hold on a suitable environment.
  In particular, we construct the environment by taking directly the result of the assignment function
  so that every variable evaluate to the trace cell value which is assigned to
-/
@[simp]
def constraints_hold_on_window {F : Type} {M W : ℕ+} [Field F]
    {S : Type -> Type} [StructuredElements S F]
    (table : TableConstraint F M W Unit) (window: TraceOfLength F S M W) : Prop :=
  let ((ctx, ops), ()) := table TableContext.empty

  -- construct an env by simply taking the result of the assignment function
  let env : ℕ -> F := fun x =>
    match ctx.assignment x with
    | ⟨i, j⟩ => window.get i j

  -- then we fold over allocated sub-circuits
  -- lifting directly to the soundness of the sub-circuit
  foldl ops env
  where
  @[simp]
  foldl : List (TableConstraintOperation F M W) -> (env: ℕ -> F) -> Prop
  | [], _ => true
  | op :: ops, env =>
    match op with
    | TableConstraintOperation.Allocate {soundness ..} => soundness env ∧ foldl ops env
    | _ => foldl ops env

def output {α : Type} {F : Type} {M W : ℕ+} [Field F] (table : TableConstraint F M W α) : α :=
  let ((_, _), a) := table TableContext.empty
  a

@[simp]
def witness_cell {F : Type} {M W : ℕ+} [Field F] (off : CellOffset M W) (compute : Unit → F): TableConstraint F M W (Variable F) :=
  as_table_operation fun ctx =>
  (TableConstraintOperation.Witness off compute, ⟨ ctx.subContext.offset, compute ⟩)

@[simp]
def get_cell {F : Type} {M W : ℕ+} [Field F] (off : CellOffset M W): TableConstraint F M W (Variable F) :=
  as_table_operation fun ctx =>
  -- TODO: how to handle multiple withenss functions?
  (TableConstraintOperation.Witness off (fun _ => 0), ⟨ ctx.subContext.offset, (fun _ => 0) ⟩)

/--
  Get a fresh variable for each cell in the current row, then cast the variables to the
  relevanto RowType structure, and return the row.
-/
@[simp]
def get_curr_row {F : Type} {M W : ℕ+} [Field F]
    (S : Type -> Type) [StructuredElements S (Expression F)]
    (h_size : StructuredElements.size S (Expression F) = M):
    TableConstraint F M W (S (Expression F)) := do
  let vars ← do
    let v := (Vector.finRange M)
    let vs := v.map (fun i => get_cell (F:=F) (CellOffset.curr i))
    vs.mapM
  let exprs : Vector (Expression F) M := vars.map (fun v => Expression.var v)
  return (by
    rw [←h_size] at exprs
    exact StructuredElements.from_elements exprs)

@[simp]
def subcircuit
    {F : Type} {M W : ℕ+} [Field F]
    {α β : TypePair} [ProvableType F β] [ProvableType F α]
    (circuit: FormalCircuit F β α) (b: β.var) : TableConstraint F M W α.var :=
  as_table_operation fun ctx =>
  let ⟨ a, subcircuit ⟩ := Circuit.formal_circuit_to_subcircuit ctx.subContext circuit b
  (TableConstraintOperation.Allocate subcircuit, a)

@[simp]
def assertion
    {F : Type} {M W : ℕ+} [Field F]
    {β : TypePair} [ProvableType F β]
    (circuit: FormalAssertion F β) (b: β.var) : TableConstraint F M W Unit :=
  as_table_operation fun ctx =>
    let subcircuit := Circuit.formal_assertion_to_subcircuit ctx.subContext circuit b
    (TableConstraintOperation.Allocate subcircuit, ())

def assign {F : Type} {M W : ℕ+} [Field F] (v: Variable F) (off : CellOffset M W) : TableConstraint F M W Unit :=
  as_table_operation fun _ =>
  (TableConstraintOperation.Assign v off, ())

end TableConstraint


@[reducible]
def SingleRowConstraint (F : Type) [Field F] (M : ℕ+) := TableConstraint F M 1 Unit

@[reducible]
def TwoRowsConstraint (F : Type) [Field F] (M : ℕ+) := TableConstraint F M 2 Unit

inductive TableOperation (F : Type) [Field F] (M : ℕ+) where
  /--
    A `Boundary` constraint is a constraint that is applied only to a specific row
  -/
  | Boundary: ℕ -> SingleRowConstraint F M -> TableOperation F M

  /--
    An `EveryRow` constraint is a constraint that is applied to every row.
    It can only reference cells on the same row
  -/
  | EveryRow: SingleRowConstraint F M -> TableOperation F M

  /--
    An `EveryRowExceptLast` constraint is a constraint that is applied to every row except the last.
    It can reference cells from the current row, or the next row
  -/
  | EveryRowExceptLast: TwoRowsConstraint F M -> TableOperation F M


/--
  The constraints hold over a trace if the hold individually in a suitable environment, where the
  environment is derived from the `CellAssignment` functions. Intuitively, if a variable `x`
  is assigned to a field element in the trace `y: F` using a `CellAssignment` function, then ` env x = y`
-/
@[simp]
def table_constraints_hold
    {F : Type} [Field F] {M : ℕ+} {N : ℕ}
    {S : Type -> Type} [StructuredElements S F]
    (constraints : List (TableOperation F M)) (trace: TraceOfLength F S M N) : Prop :=
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
  @[simp]
  foldl (cs : List (TableOperation F M)) : Trace M F S -> (cs_iterator: List (TableOperation F M)) -> Prop
    -- if the trace has at least two rows and the constraint is a "every row except last" constraint, we apply the constraint
    | trace +> curr +> next, (TableOperation.EveryRowExceptLast constraint)::rest =>
        let others := foldl cs (trace +> curr +> next) rest
        let window : TraceOfLength F S M 2 := ⟨<+> +> curr +> next, rfl ⟩
        constraint.constraints_hold_on_window window ∧ others

    -- if the trace has at least one row and the constraint is a boundary constraint, we apply the constraint if the
    -- index is the same as the length of the remaining trace
    | trace +> row, (TableOperation.Boundary idx constraint)::rest =>
        let others := foldl cs (trace +> row) rest
        let window : TraceOfLength F S M 1 := ⟨<+> +> row, rfl⟩
        if trace.len = idx then constraint.constraints_hold_on_window window ∧ others else others

    -- if the trace has at least one row and the constraint is a "every row" constraint, we apply the constraint
    | trace +> row, (TableOperation.EveryRow constraint)::rest =>
        let others := foldl cs (trace +> row) rest
        let window : TraceOfLength F S M 1 := ⟨<+> +> row, rfl⟩
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


structure FormalTable {F : Type} [Field F] {S : Type -> Type} [StructuredElements S F] where
  -- number of columns
  M : ℕ+

  -- list of constraints that are applied over the table
  constraints : List (TableOperation F M)

  -- assumptions for the table
  assumptions {N : ℕ} : TraceOfLength F S M N -> Prop

  -- specification for the table
  spec {N : ℕ} : TraceOfLength F S M N -> Prop

  -- the soundness states that if the assumptions hold, then
  -- the constraints hold implies that the spec holds
  soundness :
    ∀ (N : ℕ) (trace: TraceOfLength F S M N),
    assumptions trace ->
    table_constraints_hold constraints trace ->
    spec trace
