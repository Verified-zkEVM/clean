import Clean.Circuit.Expression
import Clean.Circuit.Provable

variable {F: Type} {s : ℕ}

structure Table (F : Type) where
  name: String
  length: ℕ
  arity: ℕ
  row: Fin length → Vector F arity

def Table.contains (table: Table F) row := ∃ i, row = table.row i

structure Lookup (F : Type) (s : ℕ) where
  table: Table F
  entry: Vector (Expression F s) table.arity
  index: Unit → Fin table.length -- index of the entry

instance [Repr F] : Repr (Lookup F s) where
  reprPrec l _ := "(Lookup " ++ l.table.name ++ " " ++ repr l.entry ++ ")"

inductive RowIndex
  | Current
  | Next
deriving Repr

structure Cell (F : Type) where
  row: RowIndex
  column: ℕ -- index of the column
deriving Repr

variable {α : Type} [Field F]

inductive PreOperation (F : Type) (s : ℕ) where
  | Witness : (compute : Unit → F) → PreOperation F s
  | Assert : Expression F s → PreOperation F s
  | Lookup : Lookup F s → PreOperation F s
  | Assign : Cell F × Variable F s → PreOperation F s

namespace PreOperation
def toString [Repr F] : PreOperation F s → String
  | Witness _v => "Witness"
  | Assert e => "(Assert " ++ reprStr e ++ " == 0)"
  | Lookup l => reprStr l
  | Assign (c, v) => "(Assign " ++ reprStr c ++ ", " ++ reprStr v ++ ")"

instance [Repr F] : Repr (PreOperation F s) where
  reprPrec op _ := toString op

def constraints_hold (env: Fin s → F) : List (PreOperation F s) → Prop
  | [] => True
  | op :: [] => match op with
    | Assert e => e.eval_env env = 0
    | Lookup { table, entry, index := _ } =>
      table.contains (entry.map (fun e => e.eval_env env))
    | _ => True
  | op :: ops => match op with
    | Assert e => ((e.eval_env env) = 0) ∧ constraints_hold env ops
    | Lookup { table, entry, index := _ } =>
      table.contains (entry.map (fun e => e.eval_env env)) ∧ constraints_hold env ops
    | _ => constraints_hold env ops

@[simp]
def witness_length : List (PreOperation F s) → ℕ
  | [] => 0
  | (Witness _) :: ops => witness_length ops + 1
  | _ :: ops => witness_length ops

@[simp]
def env_from_vector (env: Vector (Unit -> F) s) : Fin s → F := fun i => env.get i ()

/--
Instantiate an environemtn expressed as a vector of witness generation functions at a given offset.
-/
@[simp]
def env_at_offset {n : ℕ} (env: Vector (Unit → F) n) (offset : ℕ) : ℕ → F
| i => if h : i >= offset ∧ i < offset + n then env.get ⟨ i - offset, by
  rcases h with ⟨ h1, h2 ⟩
  apply Nat.sub_lt_left_of_lt_add
  repeat assumption⟩ ()
  else 0

@[simp]
def vector_from_env (n : ℕ) (env: ℕ → F) : Vector (Unit → F) n := by
  let l := (List.map (fun i => (fun () => env i : Unit -> F)) (List.iota n))
  let v := vec l
  have h : l.length = n := by rw [List.length_map, List.length_iota]
  rw [h] at v
  exact v

end PreOperation

/--
  This type models a subcircuit: a list of operations that imply a certain spec,
  for all traces that satisfy the constraints
-/
structure SubCircuit (F: Type) [Field F] (s : ℕ) where
  ops: List (PreOperation F s)

  /--
  To construct a subcircuit we need to prove also that every expression is well-typed
  which means that the number of witnesses is equal to the addressable variables
  -/
  well_typed : s = PreOperation.witness_length ops

  -- default environment for the subcircuit
  default_env: Vector (Unit -> F) s

  -- we have a low-level notion of "the constraints hold on these operations".
  -- for convenience, we allow the framework to transform that into custom `soundness`
  -- and `completeness` statements (which may involve inputs/outputs, assumptions on inputs, etc)
  soundness : (Fin s → F) → Prop
  completeness : Prop

  -- `soundness` needs to follow from the constraints for any witness
  imply_soundness : ∀ env, PreOperation.constraints_hold env ops → soundness env

  -- `completeness` needs to imply the constraints using default witnesses
  implied_by_completeness : completeness →
    PreOperation.constraints_hold (PreOperation.env_from_vector default_env) ops

inductive Operation (F : Type) [Field F] (s : ℕ) where
  | Witness : (compute : Unit → F) → Operation F s
  | Assert : Expression F s → Operation F s
  | Lookup : Lookup F s → Operation F s
  | Assign : Cell F × Variable F s → Operation F s
  | SubCircuit {s' : ℕ} : SubCircuit F s' → Operation F s

structure Context (F : Type) [Field F] where
  offset: ℕ
  default_env: Vector (Unit -> F) offset
  operations : List (Operation F offset)

@[simp]
def Context.empty : Context F := { offset := 0, default_env := vec [], operations := [] }

namespace Operation

/--
  Lift a list of operations to a new list of operations, where newly allocated variable(s) have
  been added to the environment. This implies transforming all the variables from `Fin offset`
  to `Fin (offset + num_vars)`.
  This operation is the core to maintaining the "well-typed" property of the circuit, that is
  the fact that the number of witnesses is equal to the number of addressable variables.

  Intuitively, this is sound because if we have a context with n variables and some operations on
  them, then if we add `num_vars` variables, the operations are still well-typed in the original
  "subset" if the environment
-/
@[simp]
def lift_operations (num_vars : ℕ) (ops: List (Operation F s)) : List (Operation F (s + num_vars)) :=
  ops.map fun
    | Witness compute => Witness compute
    | Assert e => Assert (e.lift_vars (by simp))
    | Lookup l => Lookup (sorry)
    | Assign (c, v) => Assign (c, (v.lift (by simp)))
    | SubCircuit (s':=s') sub => SubCircuit (s':=s') (sorry)

@[simp]
def update_context (ctx: Context F) : Operation F ctx.offset → Context F
  | Witness compute => {
    offset := ctx.offset + 1,
    default_env := ctx.default_env.push compute
    operations := (lift_operations 1 ctx.operations) ++ [(Witness compute)]
  }
  | SubCircuit (s':=s') { ops, default_env, well_typed .. } => {
    offset := ctx.offset + PreOperation.witness_length ops,
    default_env := ctx.default_env.append (by
      rw [well_typed] at default_env
      exact default_env)
    operations := by
      let ops' := (lift_operations (PreOperation.witness_length ops) ctx.operations)
      rw [←well_typed] at ops'
      sorry
  }
  | _ => ctx

instance [Repr F] : ToString (Operation F s) where
  toString
    | Witness _v => "Witness"
    | Assert e => "(Assert " ++ reprStr e ++ " == 0)"
    | Lookup l => reprStr l
    | Assign (c, v) => "(Assign " ++ reprStr c ++ ", " ++ reprStr v ++ ")"
    | SubCircuit { ops, .. } => "(SubCircuit " ++ reprStr ops ++ ")"
end Operation

/--
  The `Circuit` monad, it is a logging monad that keeps track of the current context.
  It is well-typed in the sense that the list of operations always is indexed by
  the newly returned context offset.
  We rely on the fact that the `Context.offset` indicates also the size of the environment,
  and if we have a list of operations `Operation F ctx.offset` we are sure that are well typed for
  some context `ctx`.
  In other words, `Circuit` must return a consistent list of operations that are well-typed for the
  returned context.
-/
@[simp]
def Circuit (F : Type) [Field F] (α : Type) :=
  Context F → Context F × α

namespace Circuit
instance : Monad (Circuit F) where
  pure a ctx := (ctx, a)
  bind f g ctx :=
    let ((ctx', ops), a) := f ctx
    let ((ctx'', ops'), b) := g a ctx'
    ((ctx'', ops ++ ops'), b)

@[simp]
def run (circuit: Circuit F α) : List (Operation F s) × α :=
  let ((_, ops), a) := circuit Context.empty
  (ops, a)

@[reducible]
def operations (circuit: Circuit F α) : List (Operation F s) :=
  (circuit .empty).1.2

@[reducible]
def output (circuit: Circuit F α) (ctx : Context F := Context.empty) : α :=
  (circuit ctx).2

@[reducible]
def as_circuit (f: Context F → Operation F s × α) : Circuit F α := fun ctx  =>
  let (op, a) := f ctx
  let ctx' := op.update_context ctx
  ((ctx', [op]), a)

-- core operations we can do in a circuit

-- create a new variable
@[simp]
def witness_var (compute : Unit → F) := as_circuit (fun ctx =>
  let var: Variable F := ⟨ ctx.offset ⟩
  (Operation.Witness compute, var)
)

@[simp]
def witness (compute : Unit → F) := do
  let var ← witness_var compute
  return Expression.var var

-- add a constraint
@[simp]
def assert_zero (e: Expression F) := as_circuit (
  fun _ => (Operation.Assert e, ())
)

-- add a lookup
@[simp]
def lookup (l: Lookup F) := as_circuit (
  fun _ => (Operation.Lookup l, ())
)

-- assign a variable to a cell
@[simp]
def assign_cell (c: Cell F) (v: Variable F) := as_circuit (
  fun _ => (Operation.Assign (c, v), ())
)

/--
Type of the internal environment of a circuit.
It is a type safe vector of the witness generation functions.
-/
@[simp]
def env_type (circuit: Circuit F α) : Type :=
  let n := (circuit .empty).1.1.offset
  Vector (Unit -> F) n

-- formal concepts of soundness and completeness of a circuit

@[simp]
def constraints_hold_from_list (env: (ℕ → F)) : List (Operation F s) → Prop
  | [] => True
  | op :: [] => match op with
    | Operation.Assert e => (e.eval_env env) = 0
    | Operation.Lookup { table, entry, index := _ } =>
      table.contains (entry.map (fun e => e.eval_env env))
    | Operation.SubCircuit { soundness, .. } => soundness env
    | _ => True
  | op :: ops => match op with
    | Operation.Assert e => ((e.eval_env env) = 0) ∧ constraints_hold_from_list env ops
    | Operation.Lookup { table, entry, index := _ } =>
      table.contains (entry.map (fun e => e.eval_env env)) ∧ constraints_hold_from_list env ops
    | Operation.SubCircuit { soundness, .. } => soundness env ∧ constraints_hold_from_list env ops
    | _ => constraints_hold_from_list env ops

@[reducible, simp]
def constraints_hold (env: (ℕ → F)) (circuit: Circuit F α) (ctx : Context F := .empty) : Prop :=
  constraints_hold_from_list env (circuit ctx).1.2

variable {α β: TypePair} [ProvableType F α] [ProvableType F β]

structure FormalCircuit (F: Type) (β α: TypePair)
  [Field F] [ProvableType F α] [ProvableType F β]
  (input_vars : β.var)
where
  -- β = inputs, α = outputs
  main: Circuit F α.var

  assumptions: β.value → Prop
  spec: β.value → α.value → Prop
  default_env: β.value -> env_type main

  soundness:
    -- for all possible contexts that this circuit is instantiated on
    ∀ ctx : Context F,
    -- for all possible assignment of variables
    ∀ env: (env_type main),
    -- instantiate the env at the offset of the context
    let untyped_env := PreOperation.env_at_offset env ctx.offset
    -- for all possible input values
    ∀ b : β.value,
    Provable.eval_env untyped_env input_vars = b →
    -- if the inputs satisfy the assumptions
    assumptions b →
    -- if the constraints hold
    constraints_hold untyped_env main ctx →
    -- then the spec holds on the input and output
    let a := Provable.eval_env untyped_env (output main ctx)
    spec b a

  completeness:
    -- for all possible contexts that this circuit is instantiated on
    ∀ ctx : Context F,
    -- for all possible input values
    ∀ b : β.value,
    -- if the inputs satisfy the assumptions
    assumptions b →
    -- instantiate the default environment at the offset of the context
    let untyped_default_env := PreOperation.env_at_offset (default_env b) ctx.offset
    Provable.eval_env untyped_default_env input_vars = b →
    -- then the constraints hold on the default environemnt
    constraints_hold untyped_default_env main ctx

@[simp]
def subcircuit_soundness {b_var : β.var} (circuit: FormalCircuit F β α b_var) (a_var : α.var) (env: ℕ → F) :=
  let b := Provable.eval_env env b_var
  let a := Provable.eval_env env a_var
  circuit.assumptions b → circuit.spec b a

@[simp]
def subcircuit_completeness {b_var : β.var} (circuit: FormalCircuit F β α b_var) (b : β.value) :=
  circuit.assumptions b

@[simp]
def subcircuit_default_env {b_var : β.var} (circuit: FormalCircuit F β α b_var) :=
  circuit.default_env

/--
`FormalAssertion` models a subcircuit that is "assertion-like":
- it doesn't return anything
- by design, it is not complete: it further constrains its inputs

The notion of _soundness_ is the same as for `FormalCircuit`: some `assumptions` + constraints imply a `spec`.

However, the _completeness_ statement is weaker:
If both the assumptions AND the spec are true, then the constraints hold.

In other words, for `FormalAssertion`s the spec must be an equivalent reformulation of the constraints.
(In the case of `FormalCircuit`, the spec can be strictly weaker than the constraints.)
-/
structure FormalAssertion (F: Type) (β: TypePair) [Field F] [ProvableType F β] (input_vars : β.var) where
  main: Circuit F Unit

  assumptions: β.value → Prop
  spec: β.value → Prop
  default_env: β.value -> env_type main

  soundness:
    -- for all possible contexts that this circuit is instantiated on
    ∀ ctx : Context F,
    -- for all possible assignment of variables
    ∀ env: (env_type main),
    -- instantiate the env at the offset of the context
    let untyped_env := PreOperation.env_at_offset env ctx.offset
    -- for all possible input values
    ∀ b : β.value,
    Provable.eval_env untyped_env input_vars = b →
    -- if the inputs satisfy the assumptions
    assumptions b →
    -- if the constraints hold
    constraints_hold untyped_env main ctx →
    -- then the spec holds on the input
    spec b

  completeness:
    -- for all possible contexts that this circuit is instantiated on
    ∀ ctx : Context F,
    -- for all possible input values
    ∀ b : β.value,
    -- if the inputs satisfy the assumptions
    assumptions b →
    -- and the inputs satisfy the spec
    spec b →
    -- instantiate the default environment at the offset of the context
    let untyped_default_env := PreOperation.env_at_offset (default_env b) ctx.offset
    Provable.eval_env untyped_default_env input_vars = b →
    -- then the constraints hold on the default environemnt
    constraints_hold untyped_default_env main ctx

@[simp]
def subassertion_soundness {b_var : β.var} (circuit: FormalAssertion F β b_var) (env: ℕ → F) :=
  let b := Provable.eval_env env b_var
  circuit.assumptions b → circuit.spec b

@[simp]
def subassertion_completeness {b_var : β.var} (circuit: FormalAssertion F β b_var) (b : β.value) :=
    circuit.assumptions b ∧ circuit.spec b
end Circuit

export Circuit (witness_var witness assert_zero lookup assign_cell FormalCircuit FormalAssertion)
