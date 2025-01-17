import Mathlib.Algebra.Field.Basic
import Mathlib.Data.ZMod.Basic
import Clean.Utils.Primes
import Clean.Utils.Vector
import Clean.Circuit.Basic
import Clean.Circuit.Expression
import Clean.Circuit.Provable
import Clean.Utils.Field

import Clean.GadgetsNew.Add8.Addition8
import Clean.GadgetsNew.Equality

-- TODO: this should be something so that we can give names to the columns
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
@[simp]
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

lemma len_le_succ {M : ℕ+} {F : Type} (trace : Trace M F) (row : Row M F) : trace.len ≤ (trace +> row).len :=
  match trace with
  | <+> => by simp [Trace.len]
  | (rest +> row) =>
    let ih := len_le_succ rest row
    by simp [Trace.len, ih, Nat.le_succ]

lemma len_ge_succ_of_ge {M : ℕ+} {N : ℕ} {F : Type} (trace : Trace M F) (row : Row M F) (h : trace.len ≥ N) : (trace +> row).len ≥ N :=
  match trace with
  | <+> => by simp [Trace.len] at *; simp [h]
  | (rest +> row) => by simp [Trace.len] at *; linarith

def everyRowTwoRowsInduction' {M : ℕ+} {F : Type} {P : (t : Trace M F) → t.len ≥ 2 → Sort*}
    (base : ∀ first second (h : (<+> +> first +> second).len ≥ 2), P (<+> +> first +> second) h)
    (more : ∀ curr next : Row M F,
      ∀ (rest : Trace M F) (h : rest.len ≥ 2),
        P rest h ->
        P (rest +> curr) (len_ge_succ_of_ge _ _ h) →
        P (rest +> curr +> next) (len_ge_succ_of_ge _ _ (len_ge_succ_of_ge _ _ h)))
    : ∀ (trace : Trace M F) (h : trace.len ≥ 2), P trace h
  -- the cases where the trace is empty or has only one row are trivial,
  -- since the length is greater than 2
  | <+> => by intro h; contradiction
  | <+> +> first => by intro h; contradiction
  | <+> +> first +> second => fun h => base first second h
  | rest +> curr +> next =>
      let ih' := (everyRowTwoRowsInduction' base more (rest))
      let ih'' := (everyRowTwoRowsInduction' base more (rest +> curr))
      (Nat.lt_or_ge 2 rest.len).by_cases
        (by sorry)
        (by sorry)

@[simp]
def getLeFromBottom {M :ℕ+} {F : Type}:
    (trace : Trace M F) -> (row : Fin trace.len) -> (col : Fin M) -> F
  | _ +> currRow, ⟨0, _⟩, j => currRow j
  | rest +> _, ⟨i + 1, h⟩, j => getLeFromBottom rest ⟨i, Nat.le_of_succ_le_succ h⟩ j

end Trace


/--
  A trace of length M is a trace with exactly M rows.
-/
def TraceOfLength (F : Type) (M : ℕ+) (N : ℕ) : Type := { env : Trace M F // env.len = N }

namespace TraceOfLength

@[simp]
def get {N: ℕ+} {M : ℕ} {F : Type} : (env : TraceOfLength F N M) -> (i : Fin M) -> (j : Fin N) -> F
  | ⟨env, h⟩, i, j => env.getLeFromBottom ⟨
      M - 1 - i,
      by rw [h]; apply Nat.sub_one_sub_lt_of_lt; exact i.is_lt
    ⟩ j

/--
  Apply a proposition to every row in the trace
-/
@[simp]
def forAllRowsOfTrace {N: ℕ+} {M : ℕ} {F : Type} (trace : TraceOfLength F N M) (prop : Row N F -> Prop) : Prop :=
  inner trace.val prop
  where
  @[simp]
  inner : Trace N F -> (Row N F -> Prop) -> Prop
    | <+>, _ => true
    | rest +> row, prop => prop row ∧ inner rest prop

/--
  Apply a proposition to every row in the trace except the last one
-/
@[simp]
def forAllRowsOfTraceExceptLast {N: ℕ+} {M : ℕ} {F : Type} (trace : TraceOfLength F N M) (prop : Row N F -> Prop) : Prop :=
  inner trace.val prop
  where
  inner : Trace N F -> (Row N F -> Prop) -> Prop
    | <+>, _ => true
    | <+> +> _, _ => true
    | rest +> curr +> _, prop => prop curr ∧ inner (rest +> curr) prop


/--
  Apply a proposition, which could be dependent on the row index, to every row of the trace
-/
@[simp]
def forAllRowsOfTraceWithIndex {N: ℕ+} {M : ℕ} {F : Type} (trace : TraceOfLength F N M) (prop : Row N F -> ℕ -> Prop) : Prop :=
  inner trace.val prop
  where
  @[simp]
  inner : Trace N F -> (Row N F -> ℕ -> Prop) -> Prop
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

@[simp]
def constraints_hold_on_window {F : Type} {M W : ℕ+} [Field F]
    (table : TableConstraint F M W Unit) (window: TraceOfLength F M W) : Prop :=
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
    (constraints : List (TableOperation F M)) (trace: TraceOfLength F M N) : Prop :=
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
  foldl (cs : List (TableOperation F M)) : Trace M F -> (cs_iterator: List (TableOperation F M)) -> Prop
    -- if the trace has at least two rows and the constraint is a "every row except last" constraint, we apply the constraint
    | trace +> curr +> next, (TableOperation.EveryRowExceptLast constraint)::rest =>
        let others := foldl cs (trace +> curr +> next) rest
        let window : TraceOfLength F M 2 := ⟨<+> +> curr +> next, rfl ⟩
        constraint.constraints_hold_on_window window ∧ others

    -- if the trace has at least one row and the constraint is a boundary constraint, we apply the constraint if the
    -- index is the same as the length of the remaining trace
    | trace +> row, (TableOperation.Boundary idx constraint)::rest =>
        let others := foldl cs (trace +> row) rest
        let window : TraceOfLength F M 1 := ⟨<+> +> row, rfl⟩
        if trace.len = idx then constraint.constraints_hold_on_window window ∧ others else others

    -- if the trace has at least one row and the constraint is a "every row" constraint, we apply the constraint
    | trace +> row, (TableOperation.EveryRow constraint)::rest =>
        let others := foldl cs (trace +> row) rest
        let window : TraceOfLength F M 1 := ⟨<+> +> row, rfl⟩
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


structure FormalTable {F : Type} [Field F] where
  -- number of columns
  M : ℕ+

  -- list of constraints that are applied over the table
  constraints : List (TableOperation F M)

  -- assumptions for the table
  assumptions {N : ℕ} : TraceOfLength F M N -> Prop

  -- specification for the table
  spec {N : ℕ} : TraceOfLength F M N -> Prop

  -- the soundness states that if the assumptions hold, then
  -- the constraints hold implies that the spec holds
  soundness :
    ∀ (N : ℕ) (trace: TraceOfLength F M N),
    assumptions trace ->
    table_constraints_hold constraints trace ->
    spec trace

section Example
variable {p : ℕ} [Fact (p ≠ 0)] [Fact p.Prime]
variable [p_large_enough: Fact (p > 512)]

def add8_inline : SingleRowConstraint (F p) 3 := do
  let x <- TableConstraint.get_cell (CellOffset.curr 0)
  let y <- TableConstraint.get_cell (CellOffset.curr 1)
  let z : Expression (F p) <- TableConstraint.subcircuit Add8.circuit {x, y}

  if let var z := z then
    TableConstraint.assign z (CellOffset.curr 2)

def add8Table : List (TableOperation (F p) 3) := [
  TableOperation.EveryRow add8_inline
]

def assumptions_add8 {N : ℕ} (trace : TraceOfLength (F p) 3 N) : Prop :=
  trace.forAllRowsOfTrace (fun row => (row 0).val < 256 ∧ (row 1).val < 256)


def spec_add8 {N : ℕ} (trace : TraceOfLength (F p) 3 N) : Prop :=
  trace.forAllRowsOfTrace (fun row => (row 2).val = ((row 0).val + (row 1).val) % 256)

def formal_add8_table : FormalTable (F:=(F p)) := {
  M := 3,
  constraints := add8Table,
  assumptions := assumptions_add8,
  spec := spec_add8,
  soundness := by
    intro N trace
    simp [assumptions_add8]
    simp [add8Table, spec_add8]

    induction trace.val with
    | empty => {
      simp
    }
    | cons rest row ih => {
      -- simplify induction
      simp
      intros lookup_x lookup_y lookup_rest h_curr h_rest
      specialize ih lookup_rest h_rest
      simp [ih]

      -- now we prove a local property about the current row
      -- TODO: simp should suffice, but couldn't get it to work
      have h_varx : ((add8_inline (p:=p) { subContext := { offset := 0 }, assignment := fun _ ↦ { rowOffset := 0, column := 0 } }).1.1.2 0).column = 0
        := by rfl
      have h_vary : ((add8_inline (p:=p) { subContext := { offset := 0 }, assignment := fun _ ↦ { rowOffset := 0, column := 0 } }).1.1.2 1).column = 1
        := by rfl
      have h_varz : ((add8_inline (p:=p) { subContext := { offset := 0 }, assignment := fun _ ↦ { rowOffset := 0, column := 0 } }).1.1.2 2).column = 2
        := by rfl

      simp [ProvableType.from_values] at h_curr
      rw [h_varx, h_vary, h_varz] at h_curr

      -- and now it is easy!
      dsimp [Add8.circuit, Add8.assumptions] at h_curr
      simp [lookup_x, lookup_y] at h_curr
      assumption
    }
}

/-
  Fibonacci example
-/
def fib_relation : TwoRowsConstraint (F p) 2 := do
  let x <- TableConstraint.get_cell (CellOffset.curr 0)
  let y <- TableConstraint.get_cell (CellOffset.curr 1)
  let z : Expression (F p) <- TableConstraint.subcircuit Add8.circuit {x, y}

  if let var z := z then
    TableConstraint.assign z (CellOffset.next 1)

  let x_next <- TableConstraint.get_cell (CellOffset.next 0)
  TableConstraint.assertion Equality.circuit ⟨y, x_next⟩

def boundary_fib : SingleRowConstraint (F p) 2 := do
  let x <- TableConstraint.get_cell (CellOffset.curr 0)
  let y <- TableConstraint.get_cell (CellOffset.curr 1)
  TableConstraint.assertion Equality.circuit ⟨x, 0⟩
  TableConstraint.assertion Equality.circuit ⟨y, 1⟩

def fib_table : List (TableOperation (F p) 2) := [
  TableOperation.Boundary 0 boundary_fib,
  TableOperation.EveryRowExceptLast fib_relation,
]

def assumptions_fib {N : ℕ} (trace : TraceOfLength (F p) 2 N) : Prop :=
  N > 2 ∧
  trace.forAllRowsOfTrace (fun row => (row 1).val < 256)

def fib8 : ℕ -> ℕ
  | 0 => 0
  | 1 => 1
  | (n + 2) => (fib8 n + fib8 (n + 1)) % 256

def spec_fib {N : ℕ} (trace : TraceOfLength (F p) 2 N) : Prop :=
  trace.forAllRowsOfTraceWithIndex (λ row index =>
    ((row 0).val = fib8 index) ∧ ((row 1).val = fib8 (index + 1)))


-- heavy lifting to transform constraints into specs
-- also this proof is quite heavy computationally to check for Lean
lemma constraints_hold_sim (curr : Row 2 (F p)) (next : Row 2 (F p)) :
    TableConstraint.constraints_hold_on_window fib_relation ⟨<+> +> curr +> next, by simp⟩ →
    (ZMod.val (curr 0) < 256 → ZMod.val (curr 1) < 256 → ZMod.val (next 1) = (ZMod.val (curr 0) + ZMod.val (curr 1)) % 256) ∧ curr 1 = next 0
    := by
  intro h
  simp [Circuit.formal_assertion_to_subcircuit] at h
  simp [fib_table, ProvableType.from_values] at h

  -- TODO: we should have a better way to do this
  have var1 : ((fib_relation (p:=p) { subContext := { offset := 0 }, assignment := fun x ↦ { rowOffset := 0, column := 0 } }).1.1.2 0).column = 0
    := by rfl
  have var2 : ((fib_relation (p:=p) { subContext := { offset := 0 }, assignment := fun x ↦ { rowOffset := 0, column := 0 } }).1.1.2 1).column = 1
    := by rfl
  have var3 : ((fib_relation (p:=p) { subContext := { offset := 0 }, assignment := fun x ↦ { rowOffset := 0, column := 0 } }).1.1.2 2).column = 1
    := by rfl
  have var4 : ((fib_relation (p:=p) { subContext := { offset := 0 }, assignment := fun x ↦ { rowOffset := 0, column := 0 } }).1.1.2 4).column = 0
    := by rfl
  have var5 : ((boundary_fib (p:=p) { subContext := { offset := 0 }, assignment := fun x ↦ { rowOffset := 0, column := 0 } }).1.1.2 0).column = 0
    := by rfl
  have var6 : ((boundary_fib (p:=p) { subContext := { offset := 0 }, assignment := fun x ↦ { rowOffset := 0, column := 0 } }).1.1.2 1).column = 1
    := by rfl

  rw [var1, var2, var3] at h

  simp [Add8.circuit, Add8.assumptions, Add8.spec] at h
  simp [PreOperation.to_flat_operations, PreOperation.witness_length] at h
  rw [var4] at h
  simp [Equality.circuit, Equality.spec] at h
  assumption


def formal_fib_table : FormalTable (F:=(F p)) := {
  M := 2,
  constraints := fib_table,
  assumptions := assumptions_fib,
  spec := spec_fib,
  soundness := by
    intro N trace
    simp [assumptions_fib]
    simp [fib_table, spec_fib]

    intro N_assumption

    induction' trace.val using Trace.everyRowTwoRowsInduction with first_row curr next rest _ ih2
    · simp
    · intro lookup_h
      simp [fib_table]
      intros boundary1 boundary2
      simp [Circuit.formal_assertion_to_subcircuit, Equality.circuit, Equality.spec] at boundary1 boundary2

      have var1 : ((boundary_fib (p:=p) { subContext := { offset := 0 }, assignment := fun x ↦ { rowOffset := 0, column := 0 } }).1.1.2 0).column = 0
        := by rfl
      have var2 : ((boundary_fib (p:=p) { subContext := { offset := 0 }, assignment := fun x ↦ { rowOffset := 0, column := 0 } }).1.1.2 1).column = 1
        := by rfl

      rw [var1] at boundary1
      rw [var2] at boundary2
      simp [fib8]
      simp [boundary1, boundary2]
      apply ZMod.val_one
    · intro lookup_h
      simp at lookup_h
      -- first of all, we prove the inductive part of the spec
      unfold TraceOfLength.forAllRowsOfTraceWithIndex.inner
      intros constraints_hold
      specialize ih2 lookup_h.right

      unfold table_constraints_hold.foldl at constraints_hold
      simp only [Trace.len, Nat.succ_ne_zero, ite_false] at constraints_hold
      unfold table_constraints_hold.foldl at constraints_hold
      unfold table_constraints_hold.foldl at constraints_hold
      simp only at constraints_hold
      specialize ih2 constraints_hold.right
      simp only [ih2]

      simp at ih2
      let ⟨curr_fib0, curr_fib1⟩ := ih2.left

      -- lift the constraints to specs
      let constraints_hold := constraints_hold_sim curr next constraints_hold.left
      have ⟨add_holds, eq_holds⟩ := constraints_hold

      -- and finally now we prove the actual relations, this is fortunately very easy
      -- now that we have the specs

      have lookup_first_col : (curr 0).val < 256 := by
        -- TODO: this is true also by induction over `rest`
        sorry

      specialize add_holds lookup_first_col lookup_h.right.left

      have spec1 : (next 0).val = fib8 (rest.len + 1) := by
        apply_fun ZMod.val at eq_holds
        rw [curr_fib1] at eq_holds
        exact eq_holds.symm

      have spec2 : (next 1).val = fib8 (rest.len + 2) := by
        simp [fib8]
        rw [curr_fib0, curr_fib1] at add_holds
        assumption

      simp [spec1, spec2]
}

end Example
