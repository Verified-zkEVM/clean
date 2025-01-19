import Clean.Circuit.Expression
import Clean.Circuit.Provable

variable {F: Type}

structure Table (F : Type) where
  name: String
  length: ℕ
  arity: ℕ
  row: Fin length → Vector F arity

def Table.contains (table: Table F) row := ∃ i, row = table.row i

structure Lookup (F : Type) where
  table: Table F
  entry: Vector (Expression F) table.arity
  index: Unit → Fin table.length -- index of the entry

instance [Repr F] : Repr (Lookup F) where
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

structure Context (F : Type) where
  offset: ℕ
  witness: Vector (Unit → F) offset

@[simp]
def Context.empty : Context F :=
  { offset := 0, witness := vec [] }

def Context.default_env (ctx: Context F) : ℕ → F := fun i =>
  if h : i < ctx.offset then ctx.witness.val.get ⟨ i, by rwa [ctx.witness.prop] ⟩ () else 0

inductive PreOperation (F : Type) where
  | Witness : (compute : Unit → F) → PreOperation F
  | Assert : Expression F → PreOperation F
  | Lookup : Lookup F → PreOperation F
  | Assign : Cell F × Variable F → PreOperation F

namespace PreOperation
def toString [Repr F] : PreOperation F → String
  | Witness _v => "Witness"
  | Assert e => "(Assert " ++ reprStr e ++ " == 0)"
  | Lookup l => reprStr l
  | Assign (c, v) => "(Assign " ++ reprStr c ++ ", " ++ reprStr v ++ ")"

instance [Repr F] : Repr (PreOperation F) where
  reprPrec op _ := toString op

def constraints_hold (env: ℕ → F) : List (PreOperation F) → Prop
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

def constraints_hold_default (ctx: Context F) : List (PreOperation F) → Prop :=
  constraints_hold ctx.default_env

@[simp]
def witness_length : List (PreOperation F) → ℕ
  | [] => 0
  | (Witness _) :: ops => witness_length ops + 1
  | _ :: ops => witness_length ops

@[simp]
def witness : (l: List (PreOperation F)) → Vector (Unit → F) (witness_length l)
  | [] => ⟨ [], rfl ⟩
  | op :: ops =>
    let ⟨ w, h ⟩ := witness ops
    match op with
    | Witness compute =>
      ⟨ compute :: w, by simp [h] ⟩
    | Assert _ | Lookup _ | Assign _ =>
      ⟨ w, by simp_all only [witness_length]⟩
end PreOperation

-- this type models a subcircuit: a list of operations that imply a certain spec,
-- for all traces that satisfy the constraints
structure SubCircuit (F: Type) [Field F] where
  ops: List (PreOperation F)
  ctx: Context F

  -- we have a low-level notion of "the constraints hold on these operations".
  -- for convenience, we allow the framework to transform that into custom `soundness`
  -- and `completeness` statements (which may involve inputs/outputs, assumptions on inputs, etc)
  soundness : (ℕ → F) → Prop
  completeness : Prop

  -- `soundness` needs to follow from the constraints for any witness
  imply_soundness : ∀ env, PreOperation.constraints_hold env ops → soundness env

  -- `completeness` needs to imply the constraints using default witnesses
  implied_by_completeness : completeness → PreOperation.constraints_hold ctx.default_env ops

inductive Operation (F : Type) [Field F] where
  | Witness : (compute : Unit → F) → Operation F
  | Assert : Expression F → Operation F
  | Lookup : Lookup F → Operation F
  | Assign : Cell F × Variable F → Operation F
  | SubCircuit : SubCircuit F → Operation F

namespace Operation
@[simp]
def update_context (ctx: Context F) : Operation F → Context F
  | Witness compute => ⟨ ctx.offset + 1, ctx.witness.push compute ⟩
  | SubCircuit { ops, .. } =>
    ⟨ ctx.offset + PreOperation.witness_length ops, ctx.witness.append (PreOperation.witness ops) ⟩
  | _ => ctx

instance [Repr F] : ToString (Operation F) where
  toString
    | Witness _v => "Witness"
    | Assert e => "(Assert " ++ reprStr e ++ " == 0)"
    | Lookup l => reprStr l
    | Assign (c, v) => "(Assign " ++ reprStr c ++ ", " ++ reprStr v ++ ")"
    | SubCircuit { ops, .. } => "(SubCircuit " ++ reprStr ops ++ ")"
end Operation

@[simp]
def Circuit (F : Type) [Field F] (α : Type) :=
  Context F → (Context F × List (Operation F)) × α

namespace Circuit
instance : Monad (Circuit F) where
  pure a ctx := ((ctx, []), a)
  bind f g ctx :=
    let ((ctx', ops), a) := f ctx
    let ((ctx'', ops'), b) := g a ctx'
    ((ctx'', ops ++ ops'), b)

@[simp]
def run (circuit: Circuit F α) : List (Operation F) × α :=
  let ((_, ops), a) := circuit Context.empty
  (ops, a)

@[reducible]
def operations (circuit: Circuit F α) : List (Operation F) :=
  (circuit .empty).1.2

@[reducible]
def output (circuit: Circuit F α) (ctx : Context F := Context.empty) : α :=
  (circuit ctx).2

@[reducible]
def as_circuit (f: Context F → Operation F × α) : Circuit F α := fun ctx  =>
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

-- formal concepts of soundness and completeness of a circuit

@[simp]
def constraints_hold_from_list (env: (ℕ → F)) : List (Operation F) → Prop
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

/--
Weaker version of `constraints_hold_from_list` that captures the statement that, using the default
witness generator, checking all constraints would not fail.

For subcircuits, since we proved completeness, this only means we need to satisfy the assumptions!
-/
@[simp]
def constraints_hold_from_list_default (default_env: ℕ → F) : List (Operation F) → Prop
  | [] => True
  | op :: [] => match op with
    | Operation.Assert e => e.eval_env default_env = 0
    | Operation.Lookup { table, entry, index := _ } =>
        table.contains (entry.map (fun e => e.eval_env default_env))
    | Operation.SubCircuit { completeness, .. } => completeness
    | _ => True
  | op :: ops => match op with
    | Operation.Assert e => (e.eval_env default_env = 0) ∧ constraints_hold_from_list_default default_env ops
    | Operation.Lookup { table, entry, index := _ } =>
        table.contains (entry.map (fun e => e.eval_env default_env)) ∧ constraints_hold_from_list_default default_env ops
    | Operation.SubCircuit { completeness, .. } => completeness ∧ constraints_hold_from_list_default default_env ops
    | _ => constraints_hold_from_list_default default_env ops

@[simp]
def constraints_hold_default (circuit: Circuit F α) (ctx : Context F := Context.empty) : Prop :=
  let ((ctx', ops), _) := circuit ctx
  constraints_hold_from_list_default ctx'.default_env ops

variable {α β: TypePair} [ProvableType F α] [ProvableType F β]

structure FormalCircuit (F: Type) (β α: TypePair)
  [Field F] [ProvableType F α] [ProvableType F β]
where
  -- β = inputs, α = outputs
  main: β.var → Circuit F α.var

  assumptions: β.value → Prop
  spec: β.value → α.value → Prop

  soundness:
    -- for all environments that determine witness generation
    ∀ ctx : Context F, ∀ env: ℕ → F,
    -- for all inputs that satisfy the assumptions
    ∀ b : β.value, ∀ b_var : β.var, Provable.eval_env env b_var = b → assumptions b →
    -- if the constraints hold
    constraints_hold env (main b_var) ctx →
    -- the spec holds on the input and output
    let a := Provable.eval_env env (output (main b_var) ctx)
    spec b a

  completeness:
    ∀ ctx : Context F,
    -- for all inputs that satisfy the assumptions
    ∀ b : β.value, ∀ b_var : β.var, Provable.eval_env ctx.default_env b_var = b → assumptions b →
    -- constraints hold when using the internal witness generator
    constraints_hold_default (main b_var) ctx

@[simp]
def subcircuit_soundness (circuit: FormalCircuit F β α) (b_var : β.var) (a_var : α.var) (env: ℕ → F) :=
  let b := Provable.eval_env env b_var
  let a := Provable.eval_env env a_var
  circuit.assumptions b → circuit.spec b a

@[simp]
def subcircuit_completeness (circuit: FormalCircuit F β α) (b_var : β.var) (env: ℕ → F) :=
  let b := Provable.eval_env env b_var
  circuit.assumptions b

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
structure FormalAssertion (F: Type) (β: TypePair) [Field F] [ProvableType F β] where
  main: β.var → Circuit F Unit

  assumptions: β.value → Prop
  spec: β.value → Prop

  soundness:
    -- for all environments that determine witness generation
    ∀ ctx : Context F, ∀ env: ℕ → F,
    -- for all inputs that satisfy the assumptions
    ∀ b : β.value, ∀ b_var : β.var, Provable.eval_env env b_var = b → assumptions b →
    -- if the constraints hold
    constraints_hold env (main b_var) ctx →
    -- the spec holds
    spec b

  completeness:
    ∀ ctx : Context F,
    -- for all inputs that satisfy the assumptions AND the spec
    ∀ b : β.value, ∀ b_var : β.var, Provable.eval_env ctx.default_env b_var = b → assumptions b → spec b →
    -- the constraints hold (using the internal witness generator)
    constraints_hold_default (main b_var) ctx

@[simp]
def subassertion_soundness (circuit: FormalAssertion F β) (b_var : β.var) (env: ℕ → F) :=
  let b := Provable.eval_env env b_var
  circuit.assumptions b → circuit.spec b

@[simp]
def subassertion_completeness (circuit: FormalAssertion F β) (b_var : β.var) (env: ℕ → F) :=
  let b := Provable.eval_env env b_var
  circuit.assumptions b ∧ circuit.spec b
end Circuit

export Circuit (witness_var witness assert_zero lookup assign_cell FormalCircuit FormalAssertion)
