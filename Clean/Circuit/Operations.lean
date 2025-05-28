import Clean.Circuit.Expression
import Clean.Circuit.Provable
import Clean.Circuit.SimpGadget

variable {F: Type} [Field F] {α : Type} {n : ℕ}

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

def Operation.local_length : List (Operation F) → ℕ
  | [] => 0
  | witness m _ :: ops => m + local_length ops
  | assert _ :: ops => local_length ops
  | lookup _ :: ops => local_length ops
  | subcircuit s :: ops => s.local_length + local_length ops
