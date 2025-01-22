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

inductive PreOperation (F : Type) where
  | Witness : (compute : Environment F → F) → PreOperation F
  | Assert : Expression F → PreOperation F
  | Lookup : Lookup F → PreOperation F
namespace PreOperation
def toString [Repr F] : PreOperation F → String
  | Witness _v => "Witness"
  | Assert e => "(Assert " ++ reprStr e ++ " == 0)"
  | Lookup l => reprStr l

instance [Repr F] : Repr (PreOperation F) where
  reprPrec op _ := toString op

def constraints_hold (eval: Environment F) : List (PreOperation F) → Prop
  | [] => True
  | op :: [] => match op with
    | Assert e => eval e = 0
    | Lookup { table, entry, index := _ } =>
      table.contains (entry.map eval)
    | _ => True
  | op :: ops => match op with
    | Assert e => (eval e = 0) ∧ constraints_hold eval ops
    | Lookup { table, entry, index := _ } =>
      table.contains (entry.map eval) ∧ constraints_hold eval ops
    | _ => constraints_hold eval ops

@[simp]
def witness_length : List (PreOperation F) → ℕ
  | [] => 0
  | (Witness _) :: ops => witness_length ops + 1
  | _ :: ops => witness_length ops

@[simp]
def witness : (l: List (PreOperation F)) → _root_.Witness F (witness_length l)
  | [] => ⟨ [], rfl ⟩
  | op :: ops =>
    let ⟨ w, h ⟩ := witness ops
    match op with
    | Witness compute =>
      ⟨ compute :: w, by simp [h] ⟩
    | Assert _ | Lookup _ =>
      ⟨ w, by simp_all only [witness_length]⟩
end PreOperation

-- this type models a subcircuit: a list of operations that imply a certain spec,
-- for all traces that satisfy the constraints
structure SubCircuit (F: Type) [Field F] (offset: ℕ) where
  ops: List (PreOperation F)

  -- we have a low-level notion of "the constraints hold on these operations".
  -- for convenience, we allow the framework to transform that into custom `soundness`
  -- and `completeness` statements (which may involve inputs/outputs, assumptions on inputs, etc)
  soundness : Environment F → Prop
  completeness : Environment F → Prop

  -- `soundness` needs to follow from the constraints for any witness
  imply_soundness : ∀ env,
    PreOperation.constraints_hold env ops → soundness env

  -- `completeness` needs to imply the constraints, when using default witnesses for all _local_ variables of this circuit
  implied_by_completeness : ∀ env, env.extends_vector (PreOperation.witness ops) offset →
    completeness env → PreOperation.constraints_hold env ops

@[reducible, simp]
def SubCircuit.witness_length (sc: SubCircuit F n) := PreOperation.witness_length sc.ops

@[reducible]
def SubCircuit.witness (sc: SubCircuit F n) := PreOperation.witness sc.ops

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

/--
Singleton `Operations`, that can be collected in a plain list, for easier processing.
-/
inductive Operation (F : Type) [Field F] where
  | Witness : (compute : Environment F → F) → Operation F
  | Assert : Expression F → Operation F
  | Lookup : Lookup F → Operation F
  | SubCircuit : {n : ℕ} → SubCircuit F n → Operation F

namespace Operation
def added_witness : Operation F → ℕ
  | Witness _ => 1
  | SubCircuit s => s.witness_length
  | _ => 0

instance [Repr F] : ToString (Operation F) where
  toString
    | Witness _v => "Witness"
    | Assert e => "(Assert " ++ reprStr e ++ " == 0)"
    | Lookup l => reprStr l
    | SubCircuit { ops, .. } => "(SubCircuit " ++ reprStr ops ++ ")"
end Operation

def Operations.toList {n: ℕ} : Operations F n → List (Operation F)
  | .empty _ => []
  | .witness ops c => toList ops ++ [.Witness c]
  | .assert ops e => toList ops ++ [.Assert e]
  | .lookup ops l => toList ops ++ [.Lookup l]
  | .subcircuit ops s => toList ops ++ [.SubCircuit s]

@[reducible, simp]
def Operations.initial_offset {n: ℕ} : Operations F n → ℕ
  | .empty n => n
  | .witness ops _ => Operations.initial_offset ops
  | .assert ops _ => Operations.initial_offset ops
  | .lookup ops _ => Operations.initial_offset ops
  | .subcircuit ops s => Operations.initial_offset ops

@[simp]
def Operations.locals_length {n: ℕ} : Operations F n → ℕ
  | .empty _ => 0
  | .witness ops _ => Operations.locals_length ops + 1
  | .assert ops _ => Operations.locals_length ops
  | .lookup ops _ => Operations.locals_length ops
  | .subcircuit ops s => Operations.locals_length ops + s.witness_length

@[simp]
def Operations.local_witnesses {n: ℕ} : (ops: Operations F n) → Witness F ops.locals_length
  | .empty _ => ⟨ [], rfl ⟩
  | .witness ops c => (local_witnesses ops).push c
  | .assert ops _ => local_witnesses ops
  | .lookup ops _ => local_witnesses ops
  | .subcircuit ops s => (local_witnesses ops).append s.witness

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

def toList : OperationsList F → List (Operation F)
  | ⟨ _, ops ⟩ => ops.toList

instance : CoeOut (Operations F n) (OperationsList F) where
  coe ops := ⟨ n, ops ⟩

instance (ops) : CoeDep (OperationsList F) ops (Operations F ops.offset) where
  coe := ops.withLength
end OperationsList

@[simp]
def Circuit (F : Type) [Field F] (α : Type) :=
  OperationsList F → OperationsList F × α

@[reducible]
def Circuit.final_offset_from (circuit: Circuit F α) (offset: ℕ) : ℕ :=
  (circuit (.from_offset offset)).1.offset

@[reducible, simp]
def Circuit.from (circuit: Circuit F α) (offset : ℕ) : Operations F (circuit.final_offset_from offset) :=
  (circuit (.from_offset offset)).1.withLength

namespace Circuit
instance : Monad (Circuit F) where
  pure a ops := (ops, a)
  bind f g ops :=
    let (ops', a) := f ops
    let (ops'', b) := g a ops'
    (ops'', b)

@[reducible]
def operations (circuit: Circuit F α) (offset := 0) : List (Operation F) :=
  (circuit.from offset).toList

@[reducible]
def output (circuit: Circuit F α) (offset := 0) : α :=
  (circuit (.from_offset offset)).2

/--
It makes sense to view a circuit as a function from initial offset to `Operations × α`.
`CoeFun` doesn't seem to work, probably because `Circuit` is already a function type.
So instead we at least coerce a Nat to the initial OperationsList
-/
@[reducible]
instance : Coe ℕ (OperationsList F) where
  coe offset := .from_offset offset

-- core operations we can do in a circuit

-- create a new variable
@[simp]
def witness_var (compute : Environment F → F) : Circuit F (Variable F) := fun ops =>
  let var: Variable F := ⟨ ops.offset ⟩
  (.witness ops compute, var)

@[simp]
def witness (compute : Environment F → F) := do
  let var ← witness_var compute
  return Expression.var var

-- add a constraint
@[simp]
def assert_zero (e: Expression F) : Circuit F Unit := fun ops =>
  (.assert ops e, ())

-- add a lookup
@[simp]
def lookup (l: Lookup F) : Circuit F Unit := fun ops =>
  (.lookup ops l, ())
end Circuit

@[simp]
def Environment.extends (env: Environment F) (ops: Operations F n) : Prop :=
  -- same as `env.extends_vector ops.local_witnesses ops.initial_offset`
  ∀ i : Fin ops.locals_length, env.get (ops.initial_offset + i) = ops.local_witnesses.get i env

namespace Circuit
-- formal concepts of soundness and completeness of a circuit

@[simp]
def constraints_hold_from_list (eval: Environment F) : List (Operation F) → Prop
  | [] => True
  | op :: [] => match op with
    | Operation.Assert e => eval e = 0
    | Operation.Lookup { table, entry, index := _ } =>
      table.contains (entry.map eval)
    | Operation.SubCircuit { soundness, .. } => soundness eval
    | _ => True
  | op :: ops => match op with
    | Operation.Assert e => (eval e = 0) ∧ constraints_hold_from_list eval ops
    | Operation.Lookup { table, entry, index := _ } =>
      table.contains (entry.map eval) ∧ constraints_hold_from_list eval ops
    | Operation.SubCircuit { soundness, .. } => soundness eval ∧ constraints_hold_from_list eval ops
    | _ => constraints_hold_from_list eval ops

@[simp]
def constraints_hold_inductive {n : ℕ} (eval : Environment F) : Operations F n → Prop
  | .empty _ => True
  | .witness ops compute => constraints_hold_inductive eval ops
  | .assert ops e => constraints_hold_inductive eval ops ∧ eval e = 0
  | .lookup ops { table, entry, index := _ } =>
    constraints_hold_inductive eval ops ∧ table.contains (entry.map eval)
  | .subcircuit ops s =>
    constraints_hold_inductive eval ops ∧ PreOperation.constraints_hold eval s.ops

-- TODO should this use the inductive or the list version?
@[reducible, simp]
def constraints_hold (env: Environment F) (circuit: Circuit F α) (offset: ℕ) : Prop :=
  constraints_hold_from_list env (circuit.operations offset)

/--
Version of `constraints_hold_inductive` that replaces the statement of subcircuits with their `completeness`.
-/
@[simp]
def constraints_hold_inductive_completeness {n : ℕ} (eval : Environment F) : Operations F n → Prop
  | .empty _ => True
  | .witness ops compute => constraints_hold_inductive_completeness eval ops
  | .assert ops e =>
    let constraint := eval e = 0
    -- avoid a leading `True ∧` if ops is empty
    if let .empty m := ops then constraint else constraints_hold_inductive_completeness eval ops ∧ constraint
  | .lookup ops { table, entry, index := _ } =>
    let constraint := table.contains (entry.map eval)
    if let .empty m := ops then constraint else constraints_hold_inductive_completeness eval ops ∧ constraint
  | .subcircuit ops s =>
    let constraint := s.completeness eval
    if let .empty m := ops then constraint else constraints_hold_inductive_completeness eval ops ∧ constraint

def constraints_hold_from_list_completeness (eval: Environment F) : List (Operation F) → Prop
  | [] => True
  | op :: [] => match op with
    | .Assert e => eval e = 0
    | .Lookup { table, entry, index := _ } =>
      table.contains (entry.map eval)
    | .SubCircuit { completeness, .. } => completeness eval
    | _ => True
  | op :: ops => match op with
    | .Assert e => (eval e = 0) ∧ constraints_hold_from_list_completeness eval ops
    | .Lookup { table, entry, index := _ } =>
      table.contains (entry.map eval) ∧ constraints_hold_from_list_completeness eval ops
    | .SubCircuit { completeness, .. } => completeness eval ∧ constraints_hold_from_list_completeness eval ops
    | _ => constraints_hold_from_list_completeness eval ops

/--
Version of `constraints_hold` suitable for contexts where we prove completeness
-/
@[reducible, simp]
def constraints_hold_completeness (env: Environment F) (circuit: Circuit F α) (offset: ℕ) : Prop :=
  constraints_hold_inductive_completeness env (circuit.from offset)

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
    ∀ offset, ∀ env,
    -- for all inputs that satisfy the assumptions
    ∀ b : β.value, ∀ b_var : β.var, Provable.eval env b_var = b →
    assumptions b →
    -- if the constraints hold
    constraints_hold env (main b_var) offset →
    -- the spec holds on the input and output
    let a := Provable.eval env (output (main b_var) offset)
    spec b a

  completeness:
    -- for all environments which _use the default witness generators for local variables_
    ∀ offset : ℕ, ∀ env, ∀ b_var : β.var,
    Environment.extends env (main b_var |>.from offset) →
    -- for all inputs that satisfy the assumptions
    ∀ b : β.value, Provable.eval env b_var = b →
    assumptions b →
    -- the constraints hold
    constraints_hold_inductive_completeness env (main b_var |>.from offset)

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
    ∀ offset, ∀ env: Environment F,
    -- for all inputs that satisfy the assumptions
    ∀ b : β.value, ∀ b_var : β.var, Provable.eval env b_var = b →
    assumptions b →
    -- if the constraints hold
    constraints_hold env (main b_var) offset →
    -- the spec holds
    spec b

  completeness:
    -- for all environments which _use the default witness generators for local variables_
    ∀ offset : ℕ, ∀ env, ∀ b_var : β.var,
    Environment.extends env (main b_var |>.from offset) →
    -- for all inputs that satisfy the assumptions AND the spec
    ∀ b : β.value, Provable.eval env b_var = b →
    assumptions b → spec b →
    -- the constraints hold
    constraints_hold_completeness env (main b_var) offset

@[simp]
def subassertion_soundness (circuit: FormalAssertion F β) (b_var : β.var) (env: Environment F) :=
  let b := Provable.eval env b_var
  circuit.assumptions b → circuit.spec b

@[simp]
def subassertion_completeness (circuit: FormalAssertion F β) (b_var : β.var) (env: Environment F) :=
  let b := Provable.eval env b_var
  circuit.assumptions b ∧ circuit.spec b
end Circuit

export Circuit (witness_var witness assert_zero lookup FormalCircuit FormalAssertion)
