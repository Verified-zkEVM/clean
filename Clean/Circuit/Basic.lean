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

def Environment.extends_vector (env: Environment F) (wit: Vector F n) (offset: ℕ) : Prop :=
  ∀ i : Fin n, env.get (offset + i) = wit.get i

/--
`FlatOperation` models the operations that can be done in a circuit, in a simple/flat way.

This is an intermediary type on the way to defining the full inductive `Operations` type.
It is needed because we already need to talk about operations in the `SubCircuit` definition,
which in turn is needed to define `Operations`.
-/
inductive FlatOperation (F : Type) where
  | witness : (m: ℕ) → (Environment F → Vector F m) → FlatOperation F
  | assert : Expression F → FlatOperation F
  | lookup : Lookup F → FlatOperation F

namespace FlatOperation
def toString [Repr F] : FlatOperation F → String
  | witness _ _ => "Witness"
  | assert e => "(Assert " ++ reprStr e ++ " == 0)"
  | lookup l => reprStr l

instance [Repr F] : Repr (FlatOperation F) where
  reprPrec op _ := toString op

/--
What it means that "constraints hold" on a list of flat operations:
- For assertions, the expression must evaluate to 0
- For lookups, the evaluated entry must be in the table
-/
def constraints_hold_flat (eval: Environment F) : List (FlatOperation F) → Prop
  | [] => True
  | op :: ops => match op with
    | assert e => (eval e = 0) ∧ constraints_hold_flat eval ops
    | lookup { table, entry, .. } =>
      table.contains (entry.map eval) ∧ constraints_hold_flat eval ops
    | _ => constraints_hold_flat eval ops

@[simp]
def witness_length : List (FlatOperation F) → ℕ
  | [] => 0
  | op :: ops =>
    match op with
    | witness m _ => witness_length ops + m
    | assert _ | lookup _ => witness_length ops

@[simp]
def witnesses (env: Environment F) : (l: List (FlatOperation F)) → Vector F (witness_length l)
  | [] => .nil
  | op :: ops =>
    let ws := witnesses env ops
    match op with
    | witness m compute =>
      ⟨ (compute env).val ++ ws.val, by simp [ws.prop]; ac_rfl ⟩
    | assert _ | lookup _ =>
      ⟨ ws.val, by simp_all only [witness_length, ws.prop]⟩

@[simp]
def witness_generators : (l: List (FlatOperation F)) → Witness F (witness_length l)
  | [] => .nil
  | op :: ops =>
    let ws := witness_generators ops
    match op with
    | witness m compute =>
      ⟨ (Vector.init (fun i env => (compute env).get i)).val ++ ws.val, by simp [ws.prop]; ac_rfl ⟩
    | assert _ | lookup _ =>
      ⟨ ws.val, by simp_all only [witness_length, ws.prop]⟩
end FlatOperation

export FlatOperation (constraints_hold_flat)

/--
This is a low-level way to model a subcircuit:
A flat list of circuit operations, instantiated at a certain offset.

To enable composition of formal proofs, subcircuits come with custom `soundness` and `completeness`
statements, which have to be compatible with the subcircuit's actual constraints.
-/
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

  -- `completeness` needs to imply the constraints, when using the locally declared witness generators of this circuit
  implied_by_completeness : ∀ env, env.extends_vector (FlatOperation.witnesses env ops) offset →
    completeness env → FlatOperation.constraints_hold_flat env ops

@[reducible, simp]
def SubCircuit.witness_length (sc: SubCircuit F n) := FlatOperation.witness_length sc.ops

@[reducible]
def SubCircuit.witnesses (sc: SubCircuit F n) env := FlatOperation.witnesses env sc.ops

def SubCircuit.witness_generators (sc: SubCircuit F n) := FlatOperation.witness_generators sc.ops

/--
Core type representing the result of a circuit: a sequence of operations.

Operations are indexed by a natural number which is the offset at which new variables are created.
We use a custom inductive type, rather than a list, so that we can require the offset of subcircuits to be consistent.
-/
inductive Operations (F : Type) [Field F] : ℕ → Type where
  | empty : (n : ℕ) → Operations F n
  | witness : {n : ℕ} → Operations F n → (m: ℕ) → (compute : Environment F → Vector F m) → Operations F (n + m)
  | assert : {n : ℕ} → Operations F n → Expression F → Operations F n
  | lookup : {n : ℕ} → Operations F n → Lookup F → Operations F n
  | subcircuit : {n : ℕ} → Operations F n → (s : SubCircuit F n) → Operations F (n + s.witness_length)

-- TODO: it might make sense to make the `witness` constructor take another `length` argument
-- and return a `Vector` of witnesses, from a single `compute` function.

namespace Operations
@[reducible, simp]
def initial_offset {n: ℕ} : Operations F n → ℕ
  | .empty n => n
  | .witness ops _ _ => initial_offset ops
  | .assert ops _ => initial_offset ops
  | .lookup ops _ => initial_offset ops
  | .subcircuit ops s => initial_offset ops

@[simp]
def local_length {n: ℕ} : Operations F n → ℕ
  | .empty _ => 0
  | .witness ops m _ => local_length ops + m
  | .assert ops _ => local_length ops
  | .lookup ops _ => local_length ops
  | .subcircuit ops s => local_length ops + s.witness_length

@[simp]
def local_witnesses {n: ℕ} (env: Environment F) : (ops: Operations F n) → Vector F ops.local_length
  | .empty _ => .nil
  | .witness ops _ c => (local_witnesses env ops).append (c env)
  | .assert ops _ => local_witnesses env ops
  | .lookup ops _ => local_witnesses env ops
  | .subcircuit ops s => (local_witnesses env ops).append (s.witnesses env)

@[simp]
def witness_generators {n: ℕ} : (ops: Operations F n) → Witness F ops.local_length
  | .empty _ => .nil
  | .witness ops _ c => (witness_generators ops).append
    (Vector.init (fun i env => (c env).get i))
  | .assert ops _ => witness_generators ops
  | .lookup ops _ => witness_generators ops
  | .subcircuit ops s => (witness_generators ops).append s.witness_generators
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
def witness (ops: OperationsList F) (m: ℕ) (compute : Environment F → Vector F m) : OperationsList F :=
  ⟨ ops.offset + m, .witness ops.withLength m compute ⟩

@[reducible]
def assert (ops: OperationsList F) (e: Expression F) : OperationsList F :=
  ⟨ ops.offset, .assert ops.withLength e ⟩

@[reducible]
def lookup (ops: OperationsList F) (l: Lookup F) : OperationsList F :=
  ⟨ ops.offset, .lookup ops.withLength l ⟩

@[reducible]
def subcircuit (ops: OperationsList F) (s: SubCircuit F ops.offset) : OperationsList F :=
  ⟨ ops.offset + s.witness_length, .subcircuit ops.withLength s ⟩

/--
`Operations` and `OperationsList` are basically the same so we want easy coercions between them.
-/

instance : CoeOut (Operations F n) (OperationsList F) where
  coe ops := ⟨ n, ops ⟩

instance (ops) : CoeDep (OperationsList F) ops (Operations F ops.offset) where
  coe := ops.withLength

/--
The canonical way to create an empty `OperationsList` is to just pass in the offset
-/
@[reducible]
instance : Coe ℕ (OperationsList F) where
  coe offset := .from_offset offset

end OperationsList

/--
The monad to write circuits. Lets you use `do` notation while in the background
it builds up `Operations` that represent the circuit at a low level.

Intuitively, a `Circuit` is a function `Operations F n → Operations F n' × α` for some
return type `α`, and the monad is a state monad that keeps the `Operations` around.

For technical reasons, we wrap `Operations F n` in `OperationsList F` to get rid of the
dependent type argument; and apart from the function, we require a consistency
property to make foundational proofs work.

```
def circuit : Circuit F Unit := do
  -- witness a new variable
  let x ← witness (fun _ => 1)

  -- add a constraint
  assert_zero (x - 1) * x

  -- or add a lookup
  lookup { table := MyTable, entry := [x], ... }
```
-/
def Circuit (F : Type) [Field F] (α : Type) :=
  { run: OperationsList F → OperationsList F × α //
    -- the initial offset is preserved when applying the circuit
    ∀ ops, (run ops).1.withLength.initial_offset = ops.withLength.initial_offset }

@[reducible]
def Circuit.run (circuit: Circuit F α) := circuit.val

instance : Monad (Circuit F) where
  pure a := {
    val := fun ops => (ops, a),
    property := fun _ => rfl
  }
  bind f g := {
    val := fun ops =>
      let (ops', a) := f.run ops
      let (ops'', b) := (g a).run ops'
      (ops'', b),
    property := fun ops =>
      let res := f.run ops
      f.property ops ▸ (g res.2).property res.1
  }

namespace Circuit
@[reducible]
def final_offset (circuit: Circuit F α) (offset: ℕ) : ℕ :=
  circuit.run offset |>.fst.offset

/--
This function coercion means that we can just use `circuit n` to get the `Operations` that result
from instantiating the circuit with an initial offset `n`.

Apart from using them as a monad in actual gadgets, this is the main way to interact with circuits in
more generic, foundational theorems.
-/
instance : CoeFun (Circuit F α) (fun circuit => (offset: ℕ) → Operations F (circuit.final_offset offset)) where
  coe circuit offset := circuit.run offset |>.fst.withLength

@[reducible]
def output (circuit: Circuit F α) (offset := 0) : α :=
  circuit.run offset |>.snd

-- core operations we can do in a circuit

/-- Create a new variable -/
@[simp]
def witness_var (compute : Environment F → F) : Circuit F (Variable F) := ⟨
  fun ops =>
    let var: Variable F := ⟨ ops.offset ⟩
    (.witness ops 1 (fun env => vec [compute env]), var),
  fun _ => rfl
⟩

/-- Create a new variable, as an `Expression`. -/
@[simp]
def witness (compute : Environment F → F) := do
  let var ← witness_var compute
  return Expression.var var

@[simp]
def witness_vars (n: ℕ) (compute : Environment F → Vector F n) : Circuit F (Vector (Variable F) n) := ⟨
  fun ops =>
    let vars: Vector (Variable F) n := .init (fun i => ⟨ ops.offset + i ⟩)
    (.witness ops n compute, vars),
  fun _ => rfl
⟩

/-- Add a constraint. -/
@[simp]
def assert_zero (e: Expression F) : Circuit F Unit := ⟨
  fun ops => (.assert ops e, ()),
  fun _ => rfl
⟩

/-- Add a lookup. -/
@[simp]
def lookup (l: Lookup F) : Circuit F Unit := ⟨
  fun ops => (.lookup ops l, ()),
  fun _ => rfl
⟩
end Circuit

/--
If an environment "uses local witnesses" it means that the environment's evaluation
matches the output of the witness generator passed along with a `witness` declaration,
for all variables declared locally within the circuit.

This is the condition needed to prove completeness of a circuit.
-/
@[simp]
def Environment.uses_local_witnesses (env: Environment F) (ops: Operations F n) :=
  ∀ i : Fin ops.local_length, env.get (ops.initial_offset + i) = (ops.local_witnesses env).get i

namespace Circuit
-- formal concepts of soundness and completeness of a circuit

/--
What it means that "constraints hold" on a sequence of operations.
- For assertions, the expression must evaluate to 0
- For lookups, the evaluated entry must be in the table
- For subcircuits, the constraints must hold on the subcircuit's flat operations
-/
@[simp]
def constraints_hold {n : ℕ} (eval : Environment F) : Operations F n → Prop
  | .empty _ => True
  | .witness ops _ _ => constraints_hold eval ops
  | .assert ops e => constraints_hold eval ops ∧ eval e = 0
  | .lookup ops { table, entry, .. } =>
    constraints_hold eval ops ∧ table.contains (entry.map eval)
  | .subcircuit ops s =>
    constraints_hold eval ops ∧ constraints_hold_flat eval s.ops

/--
Version of `constraints_hold` that replaces the statement of subcircuits with their `soundness`.
-/
@[simp]
def constraints_hold.soundness {n : ℕ} (eval : Environment F) : Operations F n → Prop
  | .empty _ => True
  | .witness ops _ _ => constraints_hold eval ops
  | .assert ops e =>
    let constraint := eval e = 0
    if let .empty m := ops then constraint else (constraints_hold.soundness eval ops ∧ constraint)
  | .lookup ops { table, entry, .. } =>
    let constraint := table.contains (entry.map eval)
    if let .empty m := ops then constraint else (constraints_hold.soundness eval ops ∧ constraint)
  | .subcircuit ops s =>
    let constraint := s.soundness eval
    if let .empty m := ops then constraint else (constraints_hold.soundness eval ops ∧ constraint)

/--
Version of `constraints_hold` that replaces the statement of subcircuits with their `completeness`.
-/
@[simp]
def constraints_hold.completeness {n : ℕ} (eval : Environment F) : Operations F n → Prop
  | .empty _ => True
  | .witness ops _ _ => constraints_hold.completeness eval ops
  | .assert ops e =>
    let constraint := eval e = 0
    -- avoid a leading `True ∧` if ops is empty
    if let .empty m := ops then constraint else (constraints_hold.completeness eval ops ∧ constraint)
  | .lookup ops { table, entry, .. } =>
    let constraint := table.contains (entry.map eval)
    if let .empty m := ops then constraint else (constraints_hold.completeness eval ops ∧ constraint)
  | .subcircuit ops s =>
    let constraint := s.completeness eval
    if let .empty m := ops then constraint else (constraints_hold.completeness eval ops ∧ constraint)

variable {α β: TypePair} [ProvableType F α] [ProvableType F β]

def Soundness (F: Type) (β α: TypePair) [Field F] [ProvableType F α] [ProvableType F β]
  (main: β.var F → Circuit F (α.var F))
  (assumptions: β.value F → Prop)
  (spec: β.value F → α.value F → Prop) :=
  -- for all environments that determine witness generation
    ∀ offset, ∀ env,
    -- for all inputs that satisfy the assumptions
    ∀ b_var : β.var F, ∀ b : β.value F, eval env b_var = b →
    assumptions b →
    -- if the constraints hold
    constraints_hold.soundness env (main b_var offset) →
    -- the spec holds on the input and output
    let a := eval env (output (main b_var) offset)
    spec b a

def Completeness (F: Type) (β α: TypePair) [Field F] [ProvableType F α] [ProvableType F β]
  (main: β.var F → Circuit F (α.var F))
  (assumptions: β.value F → Prop) :=
  -- for all environments which _use the default witness generators for local variables_
  ∀ offset : ℕ, ∀ env, ∀ b_var : β.var F,
  env.uses_local_witnesses (main b_var offset) →
  -- for all inputs that satisfy the assumptions
  ∀ b : β.value F, eval env b_var = b →
  assumptions b →
  -- the constraints hold
  constraints_hold.completeness env (main b_var offset)

structure FormalCircuit (F: Type) (β α: TypePair)
  [Field F] [ProvableType F α] [ProvableType F β]
where
  -- β = inputs, α = outputs
  main: β.var F → Circuit F (α.var F)
  assumptions: β.value F → Prop
  spec: β.value F → α.value F → Prop
  soundness: Soundness F β α main assumptions spec
  completeness: Completeness F β α main assumptions

@[simp]
def subcircuit_soundness (circuit: FormalCircuit F β α) (b_var : β.var F) (a_var : α.var F) (env : Environment F) :=
  let b := eval env b_var
  let a := eval env a_var
  circuit.assumptions b → circuit.spec b a

@[simp]
def subcircuit_completeness (circuit: FormalCircuit F β α) (b_var : β.var F) (env : Environment F) :=
  let b := eval env b_var
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
  main: β.var F → Circuit F Unit

  assumptions: β.value F → Prop
  spec: β.value F → Prop

  soundness:
    -- for all environments that determine witness generation
    ∀ offset, ∀ env,
    -- for all inputs that satisfy the assumptions
    ∀ b_var : β.var F, ∀ b : β.value F, eval env b_var = b →
    assumptions b →
    -- if the constraints hold
    constraints_hold.soundness env (main b_var offset) →
    -- the spec holds
    spec b

  completeness:
    -- for all environments which _use the default witness generators for local variables_
    ∀ offset, ∀ env, ∀ b_var : β.var F,
    env.uses_local_witnesses (main b_var offset) →
    -- for all inputs that satisfy the assumptions AND the spec
    ∀ b : β.value F, eval env b_var = b →
    assumptions b → spec b →
    -- the constraints hold
    constraints_hold.completeness env (main b_var offset)

@[simp]
def subassertion_soundness (circuit: FormalAssertion F β) (b_var : β.var F) (env: Environment F) :=
  let b := eval env b_var
  circuit.assumptions b → circuit.spec b

@[simp]
def subassertion_completeness (circuit: FormalAssertion F β) (b_var : β.var F) (env: Environment F) :=
  let b := eval env b_var
  circuit.assumptions b ∧ circuit.spec b
end Circuit

export Circuit (witness_var witness witness_vars assert_zero lookup Soundness Completeness FormalCircuit FormalAssertion)

/-- move from inductive (nested) operations back to flat operations -/
def to_flat_operations {n: ℕ} : Operations F n → List (FlatOperation F)
  | .empty _ => []
  | .witness ops m c => to_flat_operations ops ++ [.witness m c]
  | .assert ops c => to_flat_operations ops ++ [.assert c]
  | .lookup ops l => to_flat_operations ops ++ [.lookup l]
  | .subcircuit ops circuit => to_flat_operations ops ++ circuit.ops

/--
Singleton `Operations`, that can be collected in a plain list, for easier processing.
-/
inductive Operation (F : Type) [Field F] where
  | witness : (m: ℕ) → (compute : Environment F → Vector F m) → Operation F
  | assert : Expression F → Operation F
  | lookup : Lookup F → Operation F
  | subcircuit : {n : ℕ} → SubCircuit F n → Operation F

namespace Operation
def added_witness : Operation F → ℕ
  | witness m _ => m
  | subcircuit s => s.witness_length
  | _ => 0

instance [Repr F] : ToString (Operation F) where
  toString
    | witness _ _ => "Witness"
    | assert e => "(Assert " ++ reprStr e ++ " == 0)"
    | lookup l => reprStr l
    | subcircuit { ops, .. } => "(SubCircuit " ++ reprStr ops ++ ")"
end Operation

def Operations.toList {n: ℕ} : Operations F n → List (Operation F)
  | .empty _ => []
  | .witness ops m c => toList ops ++ [.witness m c]
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

-- witness generation
-- TODO this is inefficient, Array should be mutable and env should be defined once at the beginning
def witnesses (circuit: Circuit F α) (offset := 0) : Array F :=
  let generators := (circuit offset).witness_generators.val
  generators.foldl (fun acc compute =>
    let env i := acc.getD i 0
    acc.push (compute ⟨ env ⟩))
  #[]
end Circuit
