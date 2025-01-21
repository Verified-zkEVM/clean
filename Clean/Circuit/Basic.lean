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

def Witness (F: Type) [Field F] (n: ℕ) := Vector (Unit → F) n

def Witness.default_env {n} (w: Witness F n) : ℕ → F := fun i =>
  if h : i < n then w.val.get ⟨ i, by rwa [w.prop] ⟩ () else 0

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

def Witness.extend {n} (wit: Witness F n) (ops: List (PreOperation F)) : Witness F (n + PreOperation.witness_length ops) :=
  wit.append (PreOperation.witness ops)

-- this type models a subcircuit: a list of operations that imply a certain spec,
-- for all traces that satisfy the constraints
structure SubCircuit (F: Type) [Field F] (offset: ℕ) where
  ops: List (PreOperation F)

  -- we have a low-level notion of "the constraints hold on these operations".
  -- for convenience, we allow the framework to transform that into custom `soundness`
  -- and `completeness` statements (which may involve inputs/outputs, assumptions on inputs, etc)
  soundness : (ℕ → F) → Prop
  completeness : Witness F offset → Prop

  -- `soundness` needs to follow from the constraints for any witness
  imply_soundness : ∀ env, PreOperation.constraints_hold env ops → soundness env

  -- `completeness` needs to imply the constraints using default witnesses
  implied_by_completeness : ∀ wit, completeness wit → PreOperation.constraints_hold (wit.extend ops).default_env ops

variable {n: ℕ}

def SubCircuit.witness_length (sc: SubCircuit F n) : ℕ := PreOperation.witness_length sc.ops

inductive Context (F : Type) [Field F] : (n: ℕ) → Type where
  | empty : Context F 0
  | witness : {n: ℕ} → Context F n → (compute : Unit → F) → Context F (n + 1)
  | assert : {n: ℕ} → Context F n → Expression F → Context F n
  | lookup : {n: ℕ} → Context F n → Lookup F → Context F n
  | assign : {n: ℕ} → Context F n → Cell F × Variable F → Context F n
  | subcircuit : {n: ℕ} → Context F n → (s: SubCircuit F n) → Context F (n + s.witness_length)

inductive Operation (F : Type) [Field F] where
  | Witness : (compute : Unit → F) → Operation F
  | Assert : Expression F → Operation F
  | Lookup : Lookup F → Operation F
  | Assign : Cell F × Variable F → Operation F
  | SubCircuit : {n : ℕ} → SubCircuit F n → Operation F

namespace Operation
def added_witness : Operation F → ℕ
  | Witness _ => 1
  | SubCircuit s => s.witness_length
  | _ => 0

-- @[simp]
-- def update_context {n: ℕ} (ctx: Context F n) : (op: Operation F) → Context F (n + op.added_witness)
--   | Witness compute => Context.witness ctx compute
--   | Assert e => Context.assert ctx e
--   | Lookup l => Context.lookup ctx l
--   | Assign c => Context.assign ctx c
--   | SubCircuit s => Context.subcircuit ctx s

instance [Repr F] : ToString (Operation F) where
  toString
    | Witness _v => "Witness"
    | Assert e => "(Assert " ++ reprStr e ++ " == 0)"
    | Lookup l => reprStr l
    | Assign (c, v) => "(Assign " ++ reprStr c ++ ", " ++ reprStr v ++ ")"
    | SubCircuit { ops, .. } => "(SubCircuit " ++ reprStr ops ++ ")"
end Operation

def Context.operations {n: ℕ} : Context F n → List (Operation F)
  | .empty => []
  | .witness ctx c => operations ctx ++ [.Witness c]
  | .assert ctx e => operations ctx ++ [.Assert e]
  | .lookup ctx l => operations ctx ++ [.Lookup l]
  | .assign ctx c => operations ctx ++ [.Assign c]
  | .subcircuit ctx s => operations ctx ++ [.SubCircuit s]

def Context.witnesses {n: ℕ} : Context F n → Witness F n
  | .empty => ⟨ [], rfl ⟩
  | .witness ctx c => (witnesses ctx).push c
  | .assert ctx _ => witnesses ctx
  | .lookup ctx _ => witnesses ctx
  | .assign ctx _ => witnesses ctx
  | .subcircuit ctx s => (witnesses ctx).extend s.ops

def Context.default_env {n: ℕ} (ctx: Context F n) : ℕ → F :=
  let witnesses := ctx.witnesses
  fun i => if h : i < n then (witnesses.val.get ⟨ i, by rwa [witnesses.prop] ⟩) () else 0

structure SomeContext (F : Type) [Field F] where
  offset: ℕ
  context: Context F offset

def context : Context F n → SomeContext F
  | ctx => ⟨ n, ctx ⟩

instance : CoeOut (Context F n) (SomeContext F) where
  coe ctx := ⟨ n, ctx ⟩

def SomeContext.empty : SomeContext F := ⟨ 0, Context.empty ⟩

def SomeContext.operations : SomeContext F → List (Operation F)
  | ⟨ _, ctx ⟩ => ctx.operations

@[simp]
def Circuit (F : Type) [Field F] (α : Type) :=
  SomeContext F → SomeContext F × α

namespace Circuit
instance : Monad (Circuit F) where
  pure a ctx := (ctx, a)
  bind f g ctx :=
    let (ctx', a) := f ctx
    let (ctx'', b) := g a ctx'
    (ctx'', b)

@[simp]
def run (circuit: Circuit F α) : List (Operation F) × α :=
  let (ctx, a) := circuit .empty
  (ctx.operations, a)

@[reducible]
def operations (circuit: Circuit F α) (ctx : SomeContext F := .empty) : List (Operation F) :=
  (circuit ctx).1.operations

@[reducible]
def output (circuit: Circuit F α) (ctx : SomeContext F := .empty) : α :=
  (circuit ctx).2

-- @[reducible]
-- def as_circuit (f: Context F → Operation F × α) : Circuit F α := fun ctx  =>
--   let (op, a) := f ctx
--   let ctx' := op.update_context ctx
--   ((ctx', [op]), a)

-- core operations we can do in a circuit

-- create a new variable
@[simp]
def witness_var (compute : Unit → F) : Circuit F (Variable F) := fun ctx =>
  let var: Variable F := ⟨ ctx.offset ⟩
  (Context.witness ctx.context compute, var)

@[simp]
def witness (compute : Unit → F) := do
  let var ← witness_var compute
  return Expression.var var

-- add a constraint
@[simp]
def assert_zero (e: Expression F) : Circuit F Unit := fun ctx =>
  (Context.assert ctx.context e, ())

-- add a lookup
@[simp]
def lookup (l: Lookup F) : Circuit F Unit := fun ctx =>
  (Context.lookup ctx.context l, ())

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
def constraints_hold (env: (ℕ → F)) (circuit: Circuit F α) (ctx : SomeContext F := .empty) : Prop :=
  constraints_hold_from_list env (circuit.operations ctx)

@[simp]
def constraints_hold_from_context {n : ℕ} (ctx: Context F n) (env : ℕ → F) : Prop :=
  match ctx with
  | .empty => True
  | .witness ctx compute => constraints_hold_from_context ctx env
  | .assert ctx e =>
    let new_constraint := e.eval_env env = 0
    match ctx with -- avoid a leading `True ∧` if ctx is empty
    | .empty => new_constraint
    | _ => constraints_hold_from_context ctx env ∧ new_constraint
  | .lookup ctx { table, entry, index := _ } =>
    let new_constraint := table.contains (entry.map (fun e => e.eval_env env))
    match ctx with
    | .empty => new_constraint
    | _ => constraints_hold_from_context ctx env ∧ new_constraint
  | .assign ctx _ => constraints_hold_from_context ctx env
  | .subcircuit ctx s =>
    let wit := ctx.witnesses
    let new_constraint := PreOperation.constraints_hold (wit.extend s.ops).default_env s.ops
    match ctx with
    | .empty => new_constraint
    | _ => constraints_hold_from_context ctx env ∧ new_constraint

/--
Weaker version of `constraints_hold_from_list` that captures the statement that, using the default
witness generator, checking all constraints would not fail.

For subcircuits, since we proved completeness, this only means we need to satisfy the assumptions!
-/
@[simp]
def constraints_hold_from_context_default {n : ℕ} : Context F n → Prop
  | .empty => True
  | .witness ctx compute => constraints_hold_from_context_default ctx
  | .assert ctx e =>
    let new_constraint := e.eval_env ctx.default_env = 0
    match ctx with -- avoid a leading `True ∧` if ctx is empty
    | .empty => new_constraint
    | _ => constraints_hold_from_context_default ctx ∧ new_constraint
  | .lookup ctx { table, entry, index := _ } =>
    let new_constraint := table.contains (entry.map (fun e => e.eval_env ctx.default_env))
    match ctx with
    | .empty => new_constraint
    | _ => constraints_hold_from_context_default ctx ∧ new_constraint
  | .assign ctx _ => constraints_hold_from_context_default ctx
  | .subcircuit ctx s =>
    let new_constraint := s.completeness ctx.witnesses
    match ctx with
    | .empty => new_constraint
    | _ => constraints_hold_from_context_default ctx ∧ new_constraint

@[simp]
def constraints_hold_default (circuit: Circuit F α) (input_ctx : SomeContext F := .empty) : Prop :=
  let (ctx, _) := circuit input_ctx
  constraints_hold_from_context_default ctx.context

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
    ∀ ctx : SomeContext F, ∀ env: ℕ → F,
    -- for all inputs that satisfy the assumptions
    ∀ b : β.value, ∀ b_var : β.var, Provable.eval_env env b_var = b →
    assumptions b →
    -- if the constraints hold
    constraints_hold env (main b_var) ctx →
    -- the spec holds on the input and output
    let a := Provable.eval_env env (output (main b_var) ctx)
    spec b a

  completeness:
    ∀ ctx : SomeContext F,
    -- for all inputs that satisfy the assumptions
    ∀ b : β.value, ∀ b_var : β.var, Provable.eval_env ctx.context.default_env b_var = b →
    assumptions b →
    -- constraints hold when using the internal witness generator
    constraints_hold_default (main b_var) ctx

@[simp]
def subcircuit_soundness (circuit: FormalCircuit F β α) (b_var : β.var) (a_var : α.var) (env: ℕ → F) :=
  let b := Provable.eval_env env b_var
  let a := Provable.eval_env env a_var
  circuit.assumptions b → circuit.spec b a

@[simp]
def subcircuit_completeness (circuit: FormalCircuit F β α) (b_var : β.var) (wit: Witness F n) :=
  let b := Provable.eval_env wit.default_env b_var
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
    ∀ ctx : SomeContext F, ∀ env: ℕ → F,
    -- for all inputs that satisfy the assumptions
    ∀ b : β.value, ∀ b_var : β.var, Provable.eval_env env b_var = b →
    assumptions b →
    -- if the constraints hold
    constraints_hold env (main b_var) ctx →
    -- the spec holds
    spec b

  completeness:
    ∀ ctx : SomeContext F,
    -- for all inputs that satisfy the assumptions AND the spec
    ∀ b : β.value, ∀ b_var : β.var, Provable.eval_env ctx.context.default_env b_var = b →
    assumptions b → spec b →
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

export Circuit (witness_var witness assert_zero lookup FormalCircuit FormalAssertion)
