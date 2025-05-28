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

def SubCircuit.offset (_: SubCircuit F n) : ℕ := n

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

def local_length : Operation F → ℕ
  | .witness m _ => m
  | .assert _ => 0
  | .lookup _ => 0
  | .subcircuit s => s.local_length
end Operation

@[reducible, circuit_norm]
def Operations (F : Type) [Field F] := List (Operation F)

def Operations.toList : Operations F → List (Operation F)
  | ops => ops

/-- move from nested operations back to flat operations -/
def to_flat_operations : Operations F → List (FlatOperation F)
  | [] => []
  | .witness m c :: ops => .witness m c :: to_flat_operations ops
  | .assert e :: ops => .assert e :: to_flat_operations ops
  | .lookup l :: ops => .lookup l :: to_flat_operations ops
  | .subcircuit s :: ops => s.ops ++ to_flat_operations ops

namespace Operations
-- @[reducible, circuit_norm]
-- def initial_offset (n) : Operations F n → ℕ
--   | .empty n => n
--   | .witness ops _ _ => initial_offset ops
--   | .assert ops _ => initial_offset ops
--   | .lookup ops _ => initial_offset ops
--   | .subcircuit ops _ => initial_offset ops

@[circuit_norm]
def local_length : Operations F → ℕ
  | [] => 0
  | .witness m _ :: ops => m + local_length ops
  | .assert _ :: ops => local_length ops
  | .lookup _ :: ops => local_length ops
  | .subcircuit s :: ops => s.local_length + local_length ops

@[circuit_norm]
def local_witnesses (env: Environment F) : (ops: Operations F) → Vector F ops.local_length
  | [] => #v[]
  | .witness _ c :: ops => c env ++ local_witnesses env ops
  | .assert _ :: ops => local_witnesses env ops
  | .lookup _ :: ops => local_witnesses env ops
  | .subcircuit s :: ops => s.witnesses env ++ local_witnesses env ops

def offset (initial_offset : ℕ) : Operations F → ℕ
  | [] => initial_offset
  | .witness m _ :: ops => offset (initial_offset + m) ops
  | .assert _ :: ops => offset initial_offset ops
  | .lookup _ :: ops => offset initial_offset ops
  | .subcircuit s :: ops => offset (initial_offset + s.local_length) ops

/-- induction principle -/
def induct {motive : Operations F → Sort*}
  (empty : motive [])
  (witness : ∀ m c ops, motive ops → motive (.witness m c :: ops))
  (assert : ∀ e ops, motive ops → motive (.assert e :: ops))
  (lookup : ∀ l ops, motive ops → motive (.lookup l :: ops))
  (subcircuit : ∀ {n} (s: SubCircuit F n) ops, motive ops → motive (.subcircuit s :: ops))
    (ops: Operations F) : motive ops :=
  match ops with
  | [] => empty
  | .witness m c :: ops => witness m c ops (induct empty witness assert lookup subcircuit ops)
  | .assert e :: ops => assert e ops (induct empty witness assert lookup subcircuit ops)
  | .lookup l :: ops => lookup l ops (induct empty witness assert lookup subcircuit ops)
  | .subcircuit s :: ops => subcircuit s ops (induct empty witness assert lookup subcircuit ops)

-- generic folding over `Operations` resulting in a proposition

structure Condition (F: Type) [Field F] where
  witness (offset: ℕ) : (m : ℕ) → (Environment F → Vector F m) → Prop := fun _ _ => True
  assert (offset: ℕ) : Expression F → Prop := fun _ => True
  lookup (offset: ℕ) : Lookup F → Prop := fun _ => True
  subcircuit (offset: ℕ) : {m : ℕ} → SubCircuit F m → Prop := fun _ => True

def forAll (offset : ℕ) (condition : Operations.Condition F) : Operations F → Prop
  | [] => True
  | .witness m c :: ops => condition.witness offset m c ∧ forAll (offset + m) condition ops
  | .assert e :: ops => condition.assert offset e ∧ forAll offset condition ops
  | .lookup l :: ops => condition.lookup offset l ∧ forAll offset condition ops
  | .subcircuit s :: ops => condition.subcircuit offset s ∧ forAll (offset + s.local_length) condition ops

theorem forAll_empty {condition : Operations.Condition F} {n: ℕ} :
  Operations.forAll n condition [] = True := rfl

theorem forAll_cons {condition : Operations.Condition F} {offset: ℕ} {op: Operation F} {ops: Operations F} :
  forAll offset condition (op :: ops) ↔
    forAll offset condition [op] ∧ forAll (offset + op.local_length) condition ops := by
  cases op <;> simp [forAll, Operation.local_length]

theorem forAll_append {condition : Operations.Condition F} {offset: ℕ} {as bs: Operations F} :
  forAll offset condition (as ++ bs) ↔
    forAll offset condition as ∧ forAll (offset + as.local_length) condition bs := by
  induction as using induct generalizing offset with
  | empty => simp [forAll_empty, local_length]
  | witness _ _ _ ih | assert _ _ ih | lookup _ _ ih | subcircuit _ _ ih =>
    simp +arith only [List.cons_append, forAll, local_length, ih, and_assoc]

/--
Subcircuits start at the same variable offset that the circuit currently is.
In practice, this is always true since subcircuits are instantiated using `subcircuit` or `assertion`.
 -/
def subcircuits_consistent (offset : ℕ) (ops : Operations F) := ops.forAll offset {
  subcircuit offset _ s := s.offset = offset
}
end Operations

structure ConsistentOperations (F : Type) [Field F] where
  ops: Operations F
  initial_offset: ℕ
  subcircuits_consistent : ops.subcircuits_consistent initial_offset

namespace ConsistentOperations
open Operations
def offset (ops: ConsistentOperations F) : ℕ := ops.ops.offset ops.initial_offset

/-- matching constructors -/
def empty (n : ℕ) : ConsistentOperations F :=
  { ops := [], initial_offset := n, subcircuits_consistent := trivial }

def witness (ops: ConsistentOperations F) (m: ℕ) (c : Environment F → Vector F m) : ConsistentOperations F where
  ops := ops.ops ++ [.witness m c]
  initial_offset := ops.initial_offset
  subcircuits_consistent := by
    simp only [Operations.subcircuits_consistent, forAll_append, forAll, and_true]
    exact ops.subcircuits_consistent

def assert (ops: ConsistentOperations F) (e: Expression F) : ConsistentOperations F where
  ops := ops.ops ++ [.assert e]
  initial_offset := ops.initial_offset
  subcircuits_consistent := by
    simp only [Operations.subcircuits_consistent, forAll_append, forAll, and_true]
    exact ops.subcircuits_consistent

def lookup (ops: ConsistentOperations F) (l: Lookup F) : ConsistentOperations F where
  ops := ops.ops ++ [.lookup l]
  initial_offset := ops.initial_offset
  subcircuits_consistent := by
    simp only [Operations.subcircuits_consistent, forAll_append, forAll, and_true]
    exact ops.subcircuits_consistent

def subcircuit (ops: ConsistentOperations F) (s: SubCircuit F n) (h_offset : ops.offset = n) : ConsistentOperations F where
  ops := ops.ops ++ [.subcircuit s]
  initial_offset := ops.initial_offset
  subcircuits_consistent := by
    simp only [Operations.subcircuits_consistent, forAll_append, forAll, and_true]
    sorry
    -- exact by
    --   dsimp only [SubCircuit.offset, SubCircuit.local_length]
    --   rw [s.local_length_eq]
    --   exact s.subcircuits_consistent

/-- induction principle -/
def ConsistentOperations.induct {motive : ConsistentOperations F → Sort*}
  (empty : ∀ n, motive (empty n))
  (witness : ∀ m c ops, motive ops → motive (witness ops m c))
  (assert : ∀ e ops, motive ops → motive (assert ops e))
  (lookup : ∀ l ops, motive ops → motive (lookup ops l))
  (subcircuit : ∀ {n} (s: SubCircuit F n) ops h_offset, motive ops → motive (subcircuit ops s h_offset))
    (ops: ConsistentOperations F) : motive ops :=
  sorry
end ConsistentOperations
