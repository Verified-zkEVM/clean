import Clean.Circuit.Expression
import Clean.Circuit.Provable
import Clean.Circuit.SimpGadget

variable {F: Type} [Field F] {α : Type} {n : ℕ}

structure Table (F : Type) where
  name: String
  arity: ℕ
  contains: Vector F arity → Prop

structure Lookup (F : Type) where
  table: Table F
  entry: Vector (Expression F) table.arity
  /-- a row in the table that the added entry is constrained to equal -/
  witness: Environment F → (row : Vector F table.arity) ×' table.contains row

structure StaticTable (F : Type) where
  name: String
  arity: ℕ
  length: ℕ
  row: Fin length → Vector F arity

def StaticTable.contains (table: StaticTable F) row := ∃ (i : Fin table.length), row = table.row i

@[circuit_norm]
def StaticTable.toTable (table: StaticTable F) : Table F where
  name := table.name
  arity := table.arity
  contains row := table.contains row

structure StaticLookup (F : Type) where
  table: StaticTable F
  entry: Vector (Expression F) table.arity
  /-- index of the entry -/
  index: Environment F → Fin table.length

@[circuit_norm]
def StaticLookup.toLookup (lookup: StaticLookup F) : Lookup F where
  table := lookup.table.toTable
  entry := lookup.entry
  witness env := ⟨ lookup.table.row (lookup.index env), ⟨ lookup.index env, rfl ⟩ ⟩

instance [Repr F] : Repr (Lookup F) where
  reprPrec l _ := "(Lookup " ++ l.table.name ++ " " ++ repr l.entry ++ ")"

@[circuit_norm]
def Environment.extends_vector (env: Environment F) (wit: Vector F n) (offset: ℕ) : Prop :=
  ∀ i : Fin n, env.get (offset + i) = wit.get i

/--
`FlatOperation` models the operations that can be done in a circuit, in a simple/flat way.

This is an intermediary type on the way to defining the full inductive `Operation` type.
It is needed because we already need to talk about operations in the `SubCircuit` definition,
which in turn is needed to define `Operation`.
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

In addition to `witness`, `assert` and `lookup`,
`Operation` can also be a `subcircuit`, which itself is essentially a list of operations.
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

/--
The number of witness variables introduced by this operation.
-/
@[circuit_norm]
def local_length : Operation F → ℕ
  | .witness m _ => m
  | .assert _ => 0
  | .lookup _ => 0
  | .subcircuit s => s.local_length
end Operation

/--
`Operations F` is an alias for `List (Operation F)`, so that we can define
methods on operations that take a self argument.
-/
@[reducible, circuit_norm]
def Operations (F : Type) [Field F] := List (Operation F)

def Operations.toList : Operations F → List (Operation F) := id

/-- move from nested operations back to flat operations -/
def to_flat_operations : Operations F → List (FlatOperation F)
  | [] => []
  | .witness m c :: ops => .witness m c :: to_flat_operations ops
  | .assert e :: ops => .assert e :: to_flat_operations ops
  | .lookup l :: ops => .lookup l :: to_flat_operations ops
  | .subcircuit s :: ops => s.ops ++ to_flat_operations ops

namespace Operations
/--
The number of witness variables introduced by these operations.
-/
@[circuit_norm]
def local_length : Operations F → ℕ
  | [] => 0
  | .witness m _ :: ops => m + local_length ops
  | .assert _ :: ops => local_length ops
  | .lookup _ :: ops => local_length ops
  | .subcircuit s :: ops => s.local_length + local_length ops

/--
The actual vector of witnesses created by these operations in the given environment.
-/
@[circuit_norm]
def local_witnesses (env: Environment F) : (ops: Operations F) → Vector F ops.local_length
  | [] => #v[]
  | .witness _ c :: ops => c env ++ local_witnesses env ops
  | .assert _ :: ops => local_witnesses env ops
  | .lookup _ :: ops => local_witnesses env ops
  | .subcircuit s :: ops => s.witnesses env ++ local_witnesses env ops

/-- Induction principle for `Operations`. -/
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

/--
A `Condition` lets you define a predicate on operations, given the type and content of the
current operation as well as the current offset.
-/
structure Condition (F: Type) [Field F] where
  witness (offset: ℕ) : (m : ℕ) → (Environment F → Vector F m) → Prop := fun _ _ => True
  assert (offset: ℕ) : Expression F → Prop := fun _ => True
  lookup (offset: ℕ) : Lookup F → Prop := fun _ => True
  subcircuit (offset: ℕ) : {m : ℕ} → SubCircuit F m → Prop := fun _ => True

@[circuit_norm]
def Condition.apply (condition: Condition F) (offset: ℕ) : Operation F → Prop
  | .witness m c => condition.witness offset m c
  | .assert e => condition.assert offset e
  | .lookup l => condition.lookup offset l
  | .subcircuit s => condition.subcircuit offset s

/--
Given a `Condition`, `forAll` is true iff all operations in the list satisfy the condition, at their respective offsets.
The function expects the initial offset as an argument.
-/
def forAll (offset : ℕ) (condition : Condition F) : Operations F → Prop
  | [] => True
  | .witness m c :: ops => condition.witness offset m c ∧ forAll (m + offset) condition ops
  | .assert e :: ops => condition.assert offset e ∧ forAll offset condition ops
  | .lookup l :: ops => condition.lookup offset l ∧ forAll offset condition ops
  | .subcircuit s :: ops => condition.subcircuit offset s ∧ forAll (s.local_length + offset) condition ops

/--
Subcircuits start at the same variable offset that the circuit currently is.
In practice, this is always true since subcircuits are instantiated using `subcircuit` or `assertion`.
 -/
 @[circuit_norm]
def subcircuits_consistent (offset : ℕ) (ops : Operations F) := ops.forAll offset {
  subcircuit offset {n} _ := n = offset
}

/--
Induction principle for operations _with subcircuit consistency_.

The differences to `induct` are:
- in addition to the operations, we also pass along the initial offset `n`
- in the subcircuit case, the subcircuit offset is the same as the initial offset
-/
def induct_consistent {motive : (ops : Operations F) → (n : ℕ) → ops.subcircuits_consistent n → Sort*}
  (empty : ∀ n, motive [] n trivial)
  (witness : ∀ n m c ops {h}, motive ops (m + n) h →
    motive (.witness m c :: ops) n (by simp_all [subcircuits_consistent, forAll]))
  (assert : ∀ n e ops {h}, motive ops n h →
    motive (.assert e :: ops) n (by simp_all [subcircuits_consistent, forAll]))
  (lookup : ∀ n l ops {h}, motive ops n h →
    motive (.lookup l :: ops) n (by simp_all [subcircuits_consistent, forAll]))
  (subcircuit : ∀ n (s: SubCircuit F n) ops {h}, motive ops (s.local_length + n) h →
    motive (.subcircuit s :: ops) n (by simp_all [subcircuits_consistent, forAll]))
    (ops : Operations F) (n : ℕ) (h: ops.subcircuits_consistent n) : motive ops n h :=
  motive' ops n h
where motive' : (ops: Operations F) → (n : ℕ) → (h : ops.subcircuits_consistent n) → motive ops n h
  | [], n, _ => empty n
  | .witness m c :: ops, n, h | .assert e :: ops, n, h | .lookup e :: ops, n, h => by
    rw [subcircuits_consistent, forAll] at h
    first
    | exact witness _ _ _ _ (motive' ops _ h.right)
    | exact assert _ _ _ (motive' ops _ h.right)
    | exact lookup _ _ _ (motive' ops _ h.right)
  | .subcircuit s :: ops, n', h => by
    rename_i n
    rw [subcircuits_consistent, forAll] at h
    have n_eq : n = n' := h.left
    subst n_eq
    exact subcircuit n s ops (motive' ops _ h.right)
end Operations
