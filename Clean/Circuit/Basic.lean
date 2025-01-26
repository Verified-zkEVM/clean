import Clean.Circuit.Expression
import Clean.Circuit.Provable

variable {F: Type} [Field F]

structure Table (F : Type) where
  name: String
  length: ℕ
  arity: ℕ
  row: Fin length → Vector F arity

def Table.contains (table: Table F) row := ∃ i, row = table.row i

structure Lookup (F : Type) where
  table: Table F
  entry: Vector (Expression F) table.arity
  index: Environment F → Fin table.length -- index of the entry

instance [Repr F] : Repr (Lookup F) where
  reprPrec l _ := "(Lookup " ++ l.table.name ++ " " ++ repr l.entry ++ ")"

variable {α : Type} {n : ℕ}

def Witness (F: Type) (n: ℕ) := Vector (Environment F → F) n

def Environment.extends_vector (env: Environment F) (wit: Witness F n) (offset: ℕ) : Prop :=
  ∀ i : Fin n, env.get (offset + i) = wit.get i env

inductive FlatOperation (F : Type) where
  | witness : (compute : Environment F → F) → FlatOperation F
  | assert : Expression F → FlatOperation F
  | lookup : Lookup F → FlatOperation F

namespace FlatOperation
def toString [Repr F] : FlatOperation F → String
  | witness _v => "Witness"
  | assert e => "(Assert " ++ reprStr e ++ " == 0)"
  | lookup l => reprStr l

instance [Repr F] : Repr (FlatOperation F) where
  reprPrec op _ := toString op

def constraints_hold_flat (eval: Environment F) : List (FlatOperation F) → Prop
  | [] => True
  | op :: ops => match op with
    | assert e => (eval e = 0) ∧ constraints_hold_flat eval ops
    | lookup { table, entry, index := _ } =>
      table.contains (entry.map eval) ∧ constraints_hold_flat eval ops
    | _ => constraints_hold_flat eval ops

@[simp]
def witness_length : List (FlatOperation F) → ℕ
  | [] => 0
  | (witness _) :: ops => witness_length ops + 1
  | _ :: ops => witness_length ops

@[simp]
def witnesses : (l: List (FlatOperation F)) → Witness F (witness_length l)
  | [] => ⟨ [], rfl ⟩
  | op :: ops =>
    let ws := witnesses ops
    match op with
    | witness compute =>
      ⟨ compute :: ws.val, by simp [ws.prop] ⟩
    | assert _ | lookup _ =>
      ⟨ ws.val, by simp_all only [witness_length, ws.prop]⟩
end FlatOperation

-- this type models a subcircuit: a list of operations that imply a certain spec,
-- for all traces that satisfy the constraints
structure SubCircuit (F: Type) [Field F] (offset: ℕ) where
  ops: List (FlatOperation F)

  -- we have a low-level notion of "the constraints hold on these operations".
  -- for convenience, we allow the framework to transform that into custom `soundness`
  -- and `completeness` statements (which may involve inputs/outputs, assumptions on inputs, etc)
  soundness : Environment F → Prop
  completeness : Environment F → Prop

  -- `soundness` needs to follow from the constraints for any witness
  imply_soundness : ∀ env,
    FlatOperation.constraints_hold_flat env ops → soundness env

  -- `completeness` needs to imply the constraints, when using default witnesses for all _local_ variables of this circuit
  implied_by_completeness : ∀ env, env.extends_vector (FlatOperation.witnesses ops) offset →
    completeness env → FlatOperation.constraints_hold_flat env ops

@[reducible, simp]
def SubCircuit.witness_length (sc: SubCircuit F n) := FlatOperation.witness_length sc.ops

@[reducible]
def SubCircuit.witnesses (sc: SubCircuit F n) := FlatOperation.witnesses sc.ops

/--
Core type representing the result of a circuit: a sequence of operations.

Operations are indexed by a natural number which is the offset at which new variables are created.
We use a custom inductive type, rather than a list, so that we can require the offset of subcircuits to be consistent.
-/
inductive Operations (F : Type) [Field F] : ℕ → Type where
  | empty : (n : ℕ) → Operations F n
  | witness : {n : ℕ} → Operations F n → (compute : Environment F → F) → Operations F (n + 1)
  | assert : {n : ℕ} → Operations F n → Expression F → Operations F n
  | lookup : {n : ℕ} → Operations F n → Lookup F → Operations F n
  | subcircuit : {n : ℕ} → Operations F n → (s : SubCircuit F n) → Operations F (n + s.witness_length)

-- TODO: it might make sense to make the `witness` constructor take another `length` argument
-- and return a `Vector` of witnesses, from a single `compute` function.

namespace Operations
@[reducible, simp]
def initial_offset {n: ℕ} : Operations F n → ℕ
  | .empty n => n
  | .witness ops _ => initial_offset ops
  | .assert ops _ => initial_offset ops
  | .lookup ops _ => initial_offset ops
  | .subcircuit ops s => initial_offset ops

@[simp]
def local_length {n: ℕ} : Operations F n → ℕ
  | .empty _ => 0
  | .witness ops _ => local_length ops + 1
  | .assert ops _ => local_length ops
  | .lookup ops _ => local_length ops
  | .subcircuit ops s => local_length ops + s.witness_length

@[simp]
def local_witnesses {n: ℕ} : (ops: Operations F n) → Witness F ops.local_length
  | .empty _ => ⟨ [], rfl ⟩
  | .witness ops c => (local_witnesses ops).push c
  | .assert ops _ => local_witnesses ops
  | .lookup ops _ => local_witnesses ops
  | .subcircuit ops s => (local_witnesses ops).append s.witnesses
end Operations

/--
Helper type to remove the dependent type argument from `Operations`,
similar to converting a `Vector` to a plain `List`.
-/
structure OperationsList (F : Type) [Field F] where
  offset: ℕ
  withLength: Operations F offset

namespace OperationsList
@[reducible]
def from_offset (offset: ℕ) : OperationsList F := ⟨ offset, .empty offset ⟩

-- constructors matching `Operations`
@[reducible]
def witness (ops: OperationsList F) (compute : Environment F → F) : OperationsList F :=
  ⟨ ops.offset + 1, .witness ops.withLength compute ⟩
@[reducible]
def assert (ops: OperationsList F) (e: Expression F) : OperationsList F :=
  ⟨ ops.offset, .assert ops.withLength e ⟩
@[reducible]
def lookup (ops: OperationsList F) (l: Lookup F) : OperationsList F :=
  ⟨ ops.offset, .lookup ops.withLength l ⟩
@[reducible]
def subcircuit (ops: OperationsList F) (s: SubCircuit F ops.offset) : OperationsList F :=
  ⟨ ops.offset + s.witness_length, .subcircuit ops.withLength s ⟩

instance : CoeOut (Operations F n) (OperationsList F) where
  coe ops := ⟨ n, ops ⟩

instance (ops) : CoeDep (OperationsList F) ops (Operations F ops.offset) where
  coe := ops.withLength

/--
The canonical way to create an empty operations list is to just pass in the offset
-/
@[reducible]
instance : Coe ℕ (OperationsList F) where
  coe offset := .from_offset offset
end OperationsList

structure Circuit (F : Type) [Field F] (α : Type) where
  run: OperationsList F → OperationsList F × α
  prop: ∀ ops, (run ops).1.withLength.initial_offset = ops.withLength.initial_offset

instance : Monad (Circuit F) where
  pure a := {
    run := fun ops => (ops, a),
    prop := fun ops => rfl
  }
  bind f g := {
    run := fun ops =>
      let (ops', a) := f.run ops
      let (ops'', b) := (g a).run ops'
      (ops'', b),
    prop := fun ops => by
      have h1 := (g (f.run ops).2).prop (f.run ops).1
      have h2 := f.prop ops
      rw [h1, h2]
  }

@[reducible]
def Circuit.final_offset (circuit: Circuit F α) (offset: ℕ) : ℕ :=
  (circuit.run offset).1.offset

instance : CoeFun (Circuit F α) (fun circuit => (offset: ℕ) → Operations F (circuit.final_offset offset)) where
  coe c offset := c.run offset |>.fst.withLength

namespace Circuit
@[reducible]
def output (circuit: Circuit F α) (offset := 0) : α :=
  (circuit.run offset).2

-- core operations we can do in a circuit

-- create a new variable
@[simp]
def witness_var (compute : Environment F → F) : Circuit F (Variable F) := ⟨
  fun ops =>
    let var: Variable F := ⟨ ops.offset ⟩
    (.witness ops compute, var),
  fun _ => rfl
⟩

@[simp]
def witness (compute : Environment F → F) := do
  let var ← witness_var compute
  return Expression.var var

-- add a constraint
@[simp]
def assert_zero (e: Expression F) : Circuit F Unit := ⟨
  fun ops => (.assert ops e, ()),
  fun _ => rfl
⟩

-- add a lookup
@[simp]
def lookup (l: Lookup F) : Circuit F Unit := ⟨
  fun ops => (.lookup ops l, ()),
  fun _ => rfl
⟩
end Circuit

@[simp]
def Environment.uses_local_witnesses (env: Environment F) (ops: Operations F n) : Prop :=
  ∀ i : Fin ops.local_length, env.get (ops.initial_offset + i) = ops.local_witnesses.get i env

namespace Circuit
-- formal concepts of soundness and completeness of a circuit

@[simp]
def constraints_hold {n : ℕ} (eval : Environment F) : Operations F n → Prop
  | .empty _ => True
  | .witness ops compute => constraints_hold eval ops
  | .assert ops e => constraints_hold eval ops ∧ eval e = 0
  | .lookup ops { table, entry, .. } =>
    constraints_hold eval ops ∧ table.contains (entry.map eval)
  | .subcircuit ops s =>
    constraints_hold eval ops ∧ FlatOperation.constraints_hold_flat eval s.ops

@[simp]
def constraints_hold.soundness {n : ℕ} (eval : Environment F) : Operations F n → Prop
  | .empty _ => True
  | .witness ops compute => constraints_hold eval ops
  | .assert ops e =>
    let constraint := eval e = 0
    if let .empty m := ops then constraint else constraints_hold.soundness eval ops ∧ constraint
  | .lookup ops { table, entry, .. } =>
    let constraint := table.contains (entry.map eval)
    if let .empty m := ops then constraint else constraints_hold.soundness eval ops ∧ constraint
  | .subcircuit ops s =>
    let constraint := s.soundness eval
    if let .empty m := ops then constraint else constraints_hold.soundness eval ops ∧ constraint

/--
Version of `constraints_hold` that replaces the statement of subcircuits with their `completeness`.
-/
@[simp]
def constraints_hold.completeness {n : ℕ} (eval : Environment F) : Operations F n → Prop
  | .empty _ => True
  | .witness ops compute => constraints_hold.completeness eval ops
  | .assert ops e =>
    let constraint := eval e = 0
    -- avoid a leading `True ∧` if ops is empty
    if let .empty m := ops then constraint else constraints_hold.completeness eval ops ∧ constraint
  | .lookup ops { table, entry, index := _ } =>
    let constraint := table.contains (entry.map eval)
    if let .empty m := ops then constraint else constraints_hold.completeness eval ops ∧ constraint
  | .subcircuit ops s =>
    let constraint := s.completeness eval
    if let .empty m := ops then constraint else constraints_hold.completeness eval ops ∧ constraint

variable {α β: TypePair} [ProvableType F α] [ProvableType F β]

def Soundness (F: Type) (β α: TypePair) [Field F] [ProvableType F α] [ProvableType F β]
  (main: β.var → Circuit F α.var)
  (assumptions: β.value → Prop)
  (spec: β.value → α.value → Prop) :=
  -- for all environments that determine witness generation
    ∀ offset, ∀ env,
    -- for all inputs that satisfy the assumptions
    ∀ b_var : β.var, ∀ b : β.value, Provable.eval env b_var = b →
    assumptions b →
    -- if the constraints hold
    constraints_hold.soundness env (main b_var offset) →
    -- the spec holds on the input and output
    let a := Provable.eval env (output (main b_var) offset)
    spec b a

def Completeness (F: Type) (β α: TypePair) [Field F] [ProvableType F α] [ProvableType F β]
  (main: β.var → Circuit F α.var)
  (assumptions: β.value → Prop) :=
  -- for all environments which _use the default witness generators for local variables_
  ∀ offset : ℕ, ∀ env, ∀ b_var : β.var,
  env.uses_local_witnesses (main b_var offset) →
  -- for all inputs that satisfy the assumptions
  ∀ b : β.value, Provable.eval env b_var = b →
  assumptions b →
  -- the constraints hold
  constraints_hold.completeness env (main b_var offset)

structure FormalCircuit (F: Type) (β α: TypePair)
  [Field F] [ProvableType F α] [ProvableType F β]
where
  -- β = inputs, α = outputs
  main: β.var → Circuit F α.var
  assumptions: β.value → Prop
  spec: β.value → α.value → Prop
  soundness: Soundness F β α main assumptions spec
  completeness: Completeness F β α main assumptions

@[simp]
def subcircuit_soundness (circuit: FormalCircuit F β α) (b_var : β.var) (a_var : α.var) (env : Environment F) :=
  let b := Provable.eval env b_var
  let a := Provable.eval env a_var
  circuit.assumptions b → circuit.spec b a

@[simp]
def subcircuit_completeness (circuit: FormalCircuit F β α) (b_var : β.var) (env : Environment F) :=
  let b := Provable.eval env b_var
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
    ∀ offset, ∀ env,
    -- for all inputs that satisfy the assumptions
    ∀ b_var : β.var, ∀ b : β.value, Provable.eval env b_var = b →
    assumptions b →
    -- if the constraints hold
    constraints_hold.soundness env (main b_var offset) →
    -- the spec holds
    spec b

  completeness:
    -- for all environments which _use the default witness generators for local variables_
    ∀ offset, ∀ env, ∀ b_var : β.var,
    env.uses_local_witnesses (main b_var offset) →
    -- for all inputs that satisfy the assumptions AND the spec
    ∀ b : β.value, Provable.eval env b_var = b →
    assumptions b → spec b →
    -- the constraints hold
    constraints_hold.completeness env (main b_var offset)

@[simp]
def subassertion_soundness (circuit: FormalAssertion F β) (b_var : β.var) (env: Environment F) :=
  let b := Provable.eval env b_var
  circuit.assumptions b → circuit.spec b

@[simp]
def subassertion_completeness (circuit: FormalAssertion F β) (b_var : β.var) (env: Environment F) :=
  let b := Provable.eval env b_var
  circuit.assumptions b ∧ circuit.spec b
end Circuit

export Circuit (witness_var witness assert_zero lookup Soundness Completeness FormalCircuit FormalAssertion)

/--
Singleton `Operations`, that can be collected in a plain list, for easier processing.
-/
inductive Operation (F : Type) [Field F] where
  | witness : (compute : Environment F → F) → Operation F
  | assert : Expression F → Operation F
  | lookup : Lookup F → Operation F
  | subcircuit : {n : ℕ} → SubCircuit F n → Operation F

namespace Operation
def added_witness : Operation F → ℕ
  | witness _ => 1
  | subcircuit s => s.witness_length
  | _ => 0

instance [Repr F] : ToString (Operation F) where
  toString
    | witness _v => "Witness"
    | assert e => "(Assert " ++ reprStr e ++ " == 0)"
    | lookup l => reprStr l
    | subcircuit { ops, .. } => "(SubCircuit " ++ reprStr ops ++ ")"
end Operation

def Operations.toList {n: ℕ} : Operations F n → List (Operation F)
  | .empty _ => []
  | .witness ops c => toList ops ++ [.witness c]
  | .assert ops e => toList ops ++ [.assert e]
  | .lookup ops l => toList ops ++ [.lookup l]
  | .subcircuit ops s => toList ops ++ [.subcircuit s]

def OperationsList.toList : OperationsList F → List (Operation F)
  | ⟨ _, ops ⟩ => ops.toList

namespace Circuit
def operations (circuit: Circuit F α) (offset := 0) : List (Operation F) :=
  (circuit offset).toList

-- TODO can probably delete these

def constraints_hold_from_list.soundness (eval: Environment F) : List (Operation F) → Prop
  | [] => True
  | op :: ops => match op with
    | .assert e => (eval e = 0) ∧ constraints_hold_from_list.soundness eval ops
    | .lookup { table, entry, index := _ } =>
      table.contains (entry.map eval) ∧ constraints_hold_from_list.soundness eval ops
    | .subcircuit { soundness, .. } => soundness eval ∧ constraints_hold_from_list.soundness eval ops
    | _ => constraints_hold_from_list.soundness eval ops

def constraints_hold_from_list.completeness (eval: Environment F) : List (Operation F) → Prop
  | [] => True
  | op :: ops => match op with
    | .assert e => (eval e = 0) ∧ constraints_hold_from_list.completeness eval ops
    | .lookup { table, entry, index := _ } =>
      table.contains (entry.map eval) ∧ constraints_hold_from_list.completeness eval ops
    | .subcircuit { completeness, .. } => completeness eval ∧ constraints_hold_from_list.completeness eval ops
    | _ => constraints_hold_from_list.completeness eval ops
end Circuit
