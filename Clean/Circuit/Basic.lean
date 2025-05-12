import Clean.Circuit.Expression
import Clean.Circuit.Provable
import Clean.Circuit.SimpGadget

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

@[circuit_norm]
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
  | witness m _ => "(Witness " ++ reprStr m ++ ")"
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

@[circuit_norm]
def witness_length : List (FlatOperation F) → ℕ
  | [] => 0
  | op :: ops =>
    match op with
    | witness m _ => witness_length ops + m
    | assert _ | lookup _ => witness_length ops

@[circuit_norm]
def witnesses (env: Environment F) : (l: List (FlatOperation F)) → Vector F (witness_length l)
  | [] => #v[]
  | op :: ops =>
    let ws := witnesses env ops
    match op with
    | witness m compute =>
      ⟨ (compute env).toArray ++ ws.toArray, by
        simp only [Array.size_append, Vector.size_toArray, witness_length]; ac_rfl ⟩
    | assert _ | lookup _ =>
      ⟨ ws.toArray, by simp only [ws.size_toArray, witness_length]⟩
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
  -- for convenience, we allow the framework to transform that into custom `soundness`,
  -- `completeness` and `uses_local_witnesses` statements (which may involve inputs/outputs, assumptions on inputs, etc)
  soundness : Environment F → Prop
  completeness : Environment F → Prop
  uses_local_witnesses : Environment F → Prop

  -- for faster simplification, the subcircuit records its local witness length separately
  -- even though it could be derived from the operations
  local_length : ℕ

  -- `soundness` needs to follow from the constraints for any witness
  imply_soundness : ∀ env,
    constraints_hold_flat env ops → soundness env

  -- `completeness` needs to imply the constraints, when using the locally declared witness generators of this circuit
  implied_by_completeness : ∀ env, env.extends_vector (FlatOperation.witnesses env ops) offset →
    completeness env → constraints_hold_flat env ops

  -- `uses_local_witnesses` needs to follow from the local witness generator condition
  implied_by_local_witnesses : ∀ env, env.extends_vector (FlatOperation.witnesses env ops) offset →
    uses_local_witnesses env

  -- `local_length` must be consistent with the operations
  local_length_eq : local_length = FlatOperation.witness_length ops

@[reducible, circuit_norm]
def SubCircuit.witnesses (sc: SubCircuit F n) env := (FlatOperation.witnesses env sc.ops).cast sc.local_length_eq.symm

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
  | subcircuit : {n : ℕ} → Operations F n → (s : SubCircuit F n) → Operations F (n + s.local_length)

namespace Operations
@[reducible, circuit_norm]
def initial_offset {n: ℕ} : Operations F n → ℕ
  | .empty n => n
  | .witness ops _ _ => initial_offset ops
  | .assert ops _ => initial_offset ops
  | .lookup ops _ => initial_offset ops
  | .subcircuit ops _ => initial_offset ops

@[circuit_norm]
def local_length {n: ℕ} : Operations F n → ℕ
  | .empty _ => 0
  | .witness ops m _ => local_length ops + m
  | .assert ops _ => local_length ops
  | .lookup ops _ => local_length ops
  | .subcircuit ops s => local_length ops + s.local_length

@[circuit_norm]
def local_witnesses {n: ℕ} (env: Environment F) : (ops: Operations F n) → Vector F ops.local_length
  | .empty _ => #v[]
  | .witness ops _ c => local_witnesses env ops ++ c env
  | .assert ops _ => local_witnesses env ops
  | .lookup ops _ => local_witnesses env ops
  | .subcircuit ops s => local_witnesses env ops ++ s.witnesses env
end Operations

/--
Helper type to remove the dependent type argument from `Operations`,
similar to converting a `Vector` to a plain `List`.
-/
structure OperationsList (F : Type) [Field F] where
  offset: ℕ
  withLength: Operations F offset

namespace OperationsList
@[reducible, circuit_norm]
def from_offset (offset: ℕ) : OperationsList F := ⟨ offset, .empty offset ⟩

-- constructors matching `Operations`
@[reducible, circuit_norm]
def witness (ops: OperationsList F) (m: ℕ) (compute : Environment F → Vector F m) : OperationsList F :=
  ⟨ ops.offset + m, .witness ops.withLength m compute ⟩

@[reducible, circuit_norm]
def assert (ops: OperationsList F) (e: Expression F) : OperationsList F :=
  ⟨ ops.offset, .assert ops.withLength e ⟩

@[reducible, circuit_norm]
def lookup (ops: OperationsList F) (l: Lookup F) : OperationsList F :=
  ⟨ ops.offset, .lookup ops.withLength l ⟩

@[reducible, circuit_norm]
def subcircuit (ops: OperationsList F) (s: SubCircuit F ops.offset) : OperationsList F :=
  ⟨ ops.offset + s.local_length, .subcircuit ops.withLength s ⟩

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
@[reducible, circuit_norm]
instance : Coe ℕ (OperationsList F) where
  coe offset := .from_offset offset

end OperationsList

/--
The monad to write circuits. Lets you use `do` notation while in the background
it builds up `Operations` that represent the circuit at a low level.

Intuitively, a `Circuit` is a function `Operations F n → α × Operations F n'` for some
return type `α`, and the monad is a state monad that keeps the `Operations` around.

For technical reasons, we wrap `Operations F n` in `OperationsList F` to get rid of the
dependent type argument.

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
@[reducible]
def Circuit (F : Type) [Field F] := StateM (OperationsList F)

namespace Circuit
@[reducible, circuit_norm]
def final_offset (circuit: Circuit F α) (offset: ℕ) : ℕ :=
  circuit offset |>.snd.offset

@[reducible, circuit_norm]
def operations (circuit: Circuit F α) (offset := 0) : Operations F (circuit.final_offset offset) :=
  circuit offset |>.snd.withLength

@[reducible, circuit_norm]
def output (circuit: Circuit F α) (offset := 0) : α :=
  circuit offset |>.fst

@[reducible, circuit_norm]
def local_length (circuit: Circuit F α) (offset := 0) : ℕ :=
  (circuit.operations offset).local_length

-- core operations we can do in a circuit

/-- Create a new variable -/
@[circuit_norm]
def witness_var (compute : Environment F → F) : Circuit F (Variable F) :=
  modifyGet fun ops =>
    let var: Variable F := ⟨ ops.offset ⟩
    ⟨var, .witness ops 1 (fun env => #v[compute env])⟩

/-- Create a new variable, as an `Expression`. -/
@[circuit_norm]
def witness (compute : Environment F → F) := do
  let v ← witness_var compute
  return var v

@[circuit_norm]
def witness_vars (n: ℕ) (compute : Environment F → Vector F n) : Circuit F (Vector (Variable F) n) :=
  modifyGet fun ops =>
    let vars := Vector.mapRange n fun i => ⟨ ops.offset + i ⟩
    ⟨vars, .witness ops n compute⟩

/-- Add a constraint. -/
@[circuit_norm]
def assert_zero (e: Expression F) : Circuit F Unit :=
  modify fun ops => .assert ops e

/-- Add a lookup. -/
@[circuit_norm]
def lookup (l: Lookup F) : Circuit F Unit :=
  modify fun ops => .lookup ops l

end Circuit

/--
If an environment "uses local witnesses" it means that the environment's evaluation
matches the output of the witness generator passed along with a `witness` declaration,
for all variables declared locally within the circuit.

This is the condition needed to prove completeness of a circuit.
-/
def Environment.uses_local_witnesses (env: Environment F) : {n: ℕ} → Operations F n → Prop
  | _, .empty _ => True
  | n + _, .witness ops m c => env.uses_local_witnesses ops ∧ env.extends_vector (c env) n
  | _, .assert ops _ => env.uses_local_witnesses ops
  | _, .lookup ops _ => env.uses_local_witnesses ops
  | n + _, .subcircuit ops s => env.uses_local_witnesses ops ∧ env.extends_vector (s.witnesses env) n

/--
Modification of `uses_local_witnesses` where subcircuits replace the condition with a custom statement.
-/
@[circuit_norm]
def Environment.uses_local_witnesses_completeness (env: Environment F) : {n: ℕ} → Operations F n → Prop
  | _, .empty _ => True
  | n + _, .witness ops m c => env.uses_local_witnesses_completeness ops ∧ env.extends_vector (c env) n
  | _, .assert ops _ => env.uses_local_witnesses_completeness ops
  | _, .lookup ops _ => env.uses_local_witnesses_completeness ops
  | _, .subcircuit ops s => env.uses_local_witnesses_completeness ops ∧ s.uses_local_witnesses env

namespace Circuit
-- formal concepts of soundness and completeness of a circuit

/--
What it means that "constraints hold" on a sequence of operations.
- For assertions, the expression must evaluate to 0
- For lookups, the evaluated entry must be in the table
- For subcircuits, the constraints must hold on the subcircuit's flat operations
-/
@[circuit_norm]
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
@[circuit_norm]
def constraints_hold.soundness {n : ℕ} (eval : Environment F) : Operations F n → Prop
  | .empty _ => True
  | .witness ops _ _ => constraints_hold.soundness eval ops
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
@[circuit_norm]
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
end Circuit

section
open Circuit (constraints_hold)
variable {α β: TypeMap} [ProvableType α] [ProvableType β]

/-
Common base type for circuits that are to be used in formal proofs.

It contains the main circuit plus some of its properties in elaborated form, to make it
faster to reason about them in proofs.
-/
class ElaboratedCircuit (F: Type) [Field F] (β α: TypeMap) [ProvableType β] [ProvableType α] where
  main: Var β F → Circuit F (Var α F)

  /-- how many local witnesses this circuit introduces -/
  local_length: Var β F → ℕ

  /-- the local length must not depend on the offset. usually automatically proved by `rfl` -/
  local_length_eq : ∀ var offset, (main var).local_length offset = local_length var
    := by intros; rfl

  /-- a direct way of computing the output of this circuit (i.e. without having to unfold `main`) -/
  output : Var β F → ℕ → Var α F

  /-- correctness of `output` -/
  output_eq : ∀ var offset, (main var).output offset = output var offset
    := by intros; rfl

  /--
    technical condition needed for subcircuit consistency: the circuit must not change its initial offset.
    usually automatically proved by `rfl`.
  -/
  initial_offset_eq: ∀ var, ∀ n, (main var |>.operations n).initial_offset = n
    := by intros; rfl

attribute [circuit_norm] ElaboratedCircuit.main ElaboratedCircuit.local_length ElaboratedCircuit.output

def Soundness (F: Type) [Field F] (circuit : ElaboratedCircuit F β α)
    (assumptions: β F → Prop) (spec: β F → α F → Prop) :=
  -- for all environments that determine witness generation
  ∀ offset : ℕ, ∀ env,
  -- for all inputs that satisfy the assumptions
  ∀ b_var : Var β F, ∀ b : β F, eval env b_var = b →
  assumptions b →
  -- if the constraints hold
  constraints_hold.soundness env (circuit.main b_var |>.operations offset) →
  -- the spec holds on the input and output
  let a := eval env (circuit.output b_var offset)
  spec b a

def Completeness (F: Type) [Field F] (circuit : ElaboratedCircuit F β α)
    (assumptions: β F → Prop) :=
  -- for all environments which _use the default witness generators for local variables_
  ∀ offset : ℕ, ∀ env, ∀ b_var : Var β F,
  env.uses_local_witnesses_completeness (circuit.main b_var |>.operations offset) →
  -- for all inputs that satisfy the assumptions
  ∀ b : β F, eval env b_var = b →
  assumptions b →
  -- the constraints hold
  constraints_hold.completeness env (circuit.main b_var |>.operations offset)

structure FormalCircuit (F: Type) (β α: TypeMap) [Field F] [ProvableType α] [ProvableType β] extends ElaboratedCircuit F β α where
  -- β = inputs, α = outputs
  assumptions: β F → Prop
  spec: β F → α F → Prop
  soundness: Soundness F inferInstance assumptions spec
  completeness: Completeness F (α:=α) inferInstance assumptions

namespace Circuit
@[circuit_norm]
def subcircuit_soundness (circuit: FormalCircuit F β α) (b_var : Var β F) (offset: ℕ) (env : Environment F) :=
  let b := eval env b_var
  let a_var := circuit.output b_var offset
  let a := eval env a_var
  circuit.assumptions b → circuit.spec b a

@[circuit_norm]
def subcircuit_completeness (circuit: FormalCircuit F β α) (b_var : Var β F) (env : Environment F) :=
  let b := eval env b_var
  circuit.assumptions b
end Circuit

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
structure FormalAssertion (F: Type) (β: TypeMap) [Field F] [ProvableType β]
extends ElaboratedCircuit F β unit where
  assumptions: β F → Prop
  spec: β F → Prop

  soundness:
    -- for all environments that determine witness generation
    ∀ offset, ∀ env,
    -- for all inputs that satisfy the assumptions
    ∀ b_var : Var β F, ∀ b : β F, eval env b_var = b →
    assumptions b →
    -- if the constraints hold
    constraints_hold.soundness env (main b_var |>.operations offset) →
    -- the spec holds
    spec b

  completeness:
    -- for all environments which _use the default witness generators for local variables_
    ∀ offset, ∀ env, ∀ b_var : Var β F,
    env.uses_local_witnesses_completeness (main b_var |>.operations offset) →
    -- for all inputs that satisfy the assumptions AND the spec
    ∀ b : β F, eval env b_var = b →
    assumptions b → spec b →
    -- the constraints hold
    constraints_hold.completeness env (main b_var |>.operations offset)

  -- assertions commonly don't introduce internal witnesses, so this is a convenient default
  local_length := fun _ => 0

  output := fun _ _ => ()

namespace Circuit
@[circuit_norm]
def subassertion_soundness (circuit: FormalAssertion F β) (b_var : Var β F) (env: Environment F) :=
  let b := eval env b_var
  circuit.assumptions b → circuit.spec b

@[circuit_norm]
def subassertion_completeness (circuit: FormalAssertion F β) (b_var : Var β F) (env: Environment F) :=
  let b := eval env b_var
  circuit.assumptions b ∧ circuit.spec b
end Circuit
end

export Circuit (witness_var witness witness_vars assert_zero lookup)

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
  | subcircuit s => s.local_length
  | _ => 0

instance [Repr F] : Repr (Operation F) where
  reprPrec op _ := match op with
    | witness m _ => "(Witness " ++ reprStr m ++ ")"
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

def Circuit.operation_list (circuit: Circuit F α) (offset := 0) : List (Operation F) :=
  (circuit |>.operations offset).toList

instance [Repr F] : Repr (OperationsList F) where
  reprPrec ops _ := reprStr ops.toList

-- witness generation

def WitnessGenerators (F: Type) (n: ℕ) := Vector (Environment F → F) n

def FlatOperation.witness_generators : (l: List (FlatOperation F)) → Vector (Environment F → F) (witness_length l)
  | [] => #v[]
  | op :: ops =>
    let ws := witness_generators ops
    match op with
    | witness m compute =>
      ⟨ (Vector.mapFinRange m (fun i env => (compute env).get i)).toArray ++ ws.toArray, by
        simp only [Array.size_append, Vector.size_toArray, witness_length]; ac_rfl⟩
    | assert _ | lookup _ =>
      ⟨ ws.toArray, by simp only [ws.size_toArray, witness_length]⟩

def Operations.witness_generators {n: ℕ} : (ops: Operations F n) → Vector (Environment F → F) ops.local_length
  | .empty _ => #v[]
  | .witness ops m c => witness_generators ops ++ Vector.mapFinRange m (fun i env => (c env).get i)
  | .assert ops _ => witness_generators ops
  | .lookup ops _ => witness_generators ops
  | .subcircuit ops s => witness_generators ops ++ (s.local_length_eq ▸ FlatOperation.witness_generators s.ops)

-- TODO this is inefficient, Array should be mutable and env should be defined once at the beginning
def Circuit.witnesses (circuit: Circuit F α) (offset := 0) : Array F :=
  let generators := (circuit.operations offset).witness_generators
  generators.foldl (fun acc compute =>
    let env i := acc.getD i 0
    acc.push (compute ⟨ env ⟩))
  #[]

-- `circuit_norm` has to expand monad operations, so we need to add them to the simp set
attribute [circuit_norm] bind StateT.bind
attribute [circuit_norm] modify modifyGet MonadStateOf.modifyGet StateT.modifyGet
attribute [circuit_norm] pure StateT.pure
attribute [circuit_norm] StateT.run

/-
when simplifying lookup constraints, `circuit_norm` has to deal with expressions of the form
`(Vector.map (fun x ↦ Expression.eval env x) v#[x, y])`
that we want simplified to
`v#[x.eval env, y.eval env]`
-/
attribute [circuit_norm] Vector.map_mk List.map_toArray List.map_cons List.map_nil

-- we often need to simplify concatenated vectors, e.g. for resolving `local_witnesses`
attribute [circuit_norm] Vector.append_singleton Vector.mk_append_mk Vector.push_mk
  Array.append_singleton Array.append_empty List.push_toArray
  List.nil_append List.cons_append List.append_toArray
  Vector.mapRange_zero Vector.mapRange_succ Vector.toArray_push Array.push_toList List.append_assoc
  Vector.eq_mk Vector.mk_eq

-- simplify Vector.mapFinRange
attribute [circuit_norm] Vector.mapFinRange_succ Vector.mapFinRange_zero
    Nat.cast_zero Nat.cast_one Nat.cast_ofNat Fin.coe_eq_castSucc Fin.reduceCastSucc

-- simplify stuff like (3 : Fin 8).val = 3 % 8
attribute [circuit_norm] Fin.coe_ofNat_eq_mod

-- simplify `vector.get i` (which occurs in ProvableType definitions) and similar
attribute [circuit_norm] Vector.get Fin.val_eq_zero List.getElem_toArray
  List.getElem_cons_zero Fin.cast_eq_self List.getElem_cons_succ
  Vector.getElem_mk Vector.getElem_toArray Vector.getElem_map Fin.getElem_fin
  Fin.coe_cast Fin.isValue

-- simplify constraint expressions and +0 indices
attribute [circuit_norm] neg_mul one_mul add_zero
