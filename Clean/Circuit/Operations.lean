import Clean.Circuit.Expression
import Clean.Circuit.Lookup
import Clean.Circuit.Provable
import Clean.Circuit.SimpGadget

variable {F : Type} [Field F] {α : Type} {n : ℕ}

/--
`FlatOperation` models the operations that can be done in a circuit, in a simple/flat way.

This is an intermediary type on the way to defining the full inductive `Operation` type.
It is needed because we already need to talk about operations in the `Subcircuit` definition,
which in turn is needed to define `Operation`.
-/
inductive FlatOperation (F : Type) (ProverHint : Type) where
  | witness : (m : ℕ) → (Environment F → ProverHint → Vector F m) → FlatOperation F ProverHint
  | assert : Expression F → FlatOperation F ProverHint
  | lookup : Lookup F → FlatOperation F ProverHint

inductive NestedOperations (F : Type) (ProverHint : Type) where
  | single : FlatOperation F ProverHint → NestedOperations F ProverHint
  | nested : String × List (NestedOperations F ProverHint) → NestedOperations F ProverHint

def NestedOperations.toFlat {F : Type} {ProverHint : Type} :
    NestedOperations F ProverHint → List (FlatOperation F ProverHint)
  | .single op => [op]
  | .nested (_, lst) => List.flatMap toFlat lst

namespace FlatOperation
instance {F : Type} {ProverHint : Type} [Repr F] : Repr (FlatOperation F ProverHint) where
  reprPrec
  | witness m _, _ => "(Witness " ++ reprStr m ++ ")"
  | assert e, _ => "(Assert " ++ reprStr e ++ " == 0)"
  | lookup l, _ => reprStr l

/--
What it means that "constraints hold" on a list of flat operations:
- For assertions, the expression must evaluate to 0
- For lookups, the evaluated entry must be in the table
-/
def ConstraintsHoldFlat {F : Type} [Field F] {ProverHint : Type} (eval : Environment F) :
    List (FlatOperation F ProverHint) → Prop
  | [] => True
  | op :: ops => match op with
    | assert e => (eval e = 0) ∧ ConstraintsHoldFlat eval ops
    | lookup l => l.Contains eval ∧ ConstraintsHoldFlat eval ops
    | _ => ConstraintsHoldFlat eval ops

@[circuit_norm]
def localLength {F : Type} {ProverHint : Type} : List (FlatOperation F ProverHint) → ℕ
  | [] => 0
  | witness m _ :: ops => m + localLength ops
  | assert _ :: ops | lookup _ :: ops => localLength ops

@[circuit_norm]
def localWitnesses {F : Type} [Field F] {ProverHint : Type}
    (env : Environment F) (hint : ProverHint) :
    (l : List (FlatOperation F ProverHint)) → Vector F (localLength l)
  | [] => #v[]
  | witness _ compute :: ops => compute env hint ++ localWitnesses env hint ops
  | assert _ :: ops | lookup _ :: ops => localWitnesses env hint ops

/-- Induction principle for `FlatOperation`s. -/
def induct {F : Type} {ProverHint : Type} {motive : List (FlatOperation F ProverHint) → Sort*}
  (empty : motive [])
  (witness : ∀ m c ops, motive ops → motive (.witness m c :: ops))
  (assert : ∀ e ops, motive ops → motive (.assert e :: ops))
  (lookup : ∀ l ops, motive ops → motive (.lookup l :: ops))
    (ops : List (FlatOperation F ProverHint)) : motive ops :=
  match ops with
  | [] => empty
  | .witness m c :: ops => witness m c ops (induct empty witness assert lookup ops)
  | .assert e :: ops => assert e ops (induct empty witness assert lookup ops)
  | .lookup l :: ops => lookup l ops (induct empty witness assert lookup ops)
end FlatOperation

export FlatOperation (ConstraintsHoldFlat)

@[circuit_norm]
def Environment.ExtendsVector (env : Environment F) (wit : Vector F n) (offset : ℕ) : Prop :=
  ∀ i : Fin n, env.get (offset + i.val) = wit[i.val]

open FlatOperation in
/--
This is a low-level way to model a subcircuit:
A flat list of circuit operations, instantiated at a certain offset.

To enable composition of formal proofs, subcircuits come with custom `Soundness` and `Completeness`
statements, which have to be compatible with the subcircuit's actual constraints.
-/
structure Subcircuit (F : Type) [Field F] (ProverHint : Type) (offset : ℕ) where
  ops : NestedOperations F ProverHint

  -- we have a low-level notion of "the constraints hold on these operations".
  -- for convenience, we allow the framework to transform that into custom `Soundness`,
  -- `Completeness` and `UsesLocalWitnesses` statements (which may involve inputs/outputs, assumptions on inputs, etc)
  Soundness : Environment F → Prop
  -- `Completeness` and `UsesLocalWitnesses` take the same prover-supplied hint that drives witness generation.
  Completeness : Environment F → ProverHint → Prop
  UsesLocalWitnesses : Environment F → ProverHint → Prop

  -- for faster simplification, the subcircuit records its local witness length separately
  -- even though it could be derived from the operations
  localLength : ℕ

  -- `Soundness` needs to follow from the constraints for any witness
  imply_soundness : ∀ env,
    ConstraintsHoldFlat env ops.toFlat → Soundness env

  -- `Completeness` needs to imply the constraints, when using the locally declared witness generators at the matching prover hint
  implied_by_completeness : ∀ env hint,
    env.ExtendsVector (localWitnesses env hint ops.toFlat) offset →
    Completeness env hint → ConstraintsHoldFlat env ops.toFlat
  -- `UsesLocalWitnesses` needs to follow from the local witness generator condition, for the matching prover hint
  imply_usesLocalWitnesses : ∀ env hint,
    env.ExtendsVector (localWitnesses env hint ops.toFlat) offset →
    UsesLocalWitnesses env hint

  -- `localLength` must be consistent with the operations
  localLength_eq : localLength = FlatOperation.localLength ops.toFlat

@[reducible, circuit_norm]
def Subcircuit.witnesses {ProverHint : Type} (sc : Subcircuit F ProverHint n)
    (env : Environment F) (hint : ProverHint) :=
  (FlatOperation.localWitnesses env hint sc.ops.toFlat).cast sc.localLength_eq.symm

/--
Core type representing the result of a circuit: a sequence of operations.

In addition to `witness`, `assert` and `lookup`,
`Operation` can also be a `subcircuit`, which itself is essentially a list of operations.
-/
inductive Operation (F : Type) [Field F] (ProverHint : Type) where
  | witness : (m : ℕ) → (compute : Environment F → ProverHint → Vector F m) → Operation F ProverHint
  | assert : Expression F → Operation F ProverHint
  | lookup : Lookup F → Operation F ProverHint
  | subcircuit : {n : ℕ} → Subcircuit F ProverHint n → Operation F ProverHint

namespace Operation
instance {F : Type} [Field F] {ProverHint : Type} [Repr F] : Repr (Operation F ProverHint) where
  reprPrec op _ := match op with
    | witness m _ => "(Witness " ++ reprStr m ++ ")"
    | assert e => "(Assert " ++ reprStr e ++ " == 0)"
    | lookup l => reprStr l
    | subcircuit { ops, .. } => "(Subcircuit " ++ reprStr ops.toFlat ++ ")"

/--
The number of witness variables introduced by this operation.
-/
@[circuit_norm]
def localLength {F : Type} [Field F] {ProverHint : Type} : Operation F ProverHint → ℕ
  | .witness m _ => m
  | .assert _ => 0
  | .lookup _ => 0
  | .subcircuit s => s.localLength

def localWitnesses {F : Type} [Field F] {ProverHint : Type}
    (env : Environment F) (hint : ProverHint) :
    (op : Operation F ProverHint) → Vector F op.localLength
  | .witness _ c => c env hint
  | .assert _ => #v[]
  | .lookup _ => #v[]
  | .subcircuit s => s.witnesses env hint
end Operation

/--
`Operations F ProverHint` is an alias for `List (Operation F ProverHint)`, so that we can define
methods on operations that take a self argument.
-/
@[reducible, circuit_norm]
def Operations (F : Type) [Field F] (ProverHint : Type) := List (Operation F ProverHint)

namespace Operations
def toList {F : Type} [Field F] {ProverHint : Type} :
    Operations F ProverHint → List (Operation F ProverHint) := id

/-- move from nested operations back to flat operations -/
def toFlat {F : Type} [Field F] {ProverHint : Type} :
    Operations F ProverHint → List (FlatOperation F ProverHint)
  | [] => []
  | .witness m c :: ops => .witness m c :: toFlat ops
  | .assert e :: ops => .assert e :: toFlat ops
  | .lookup l :: ops => .lookup l :: toFlat ops
  | .subcircuit s :: ops => s.ops.toFlat ++ toFlat ops

def toNested {F : Type} [Field F] {ProverHint : Type} :
    Operations F ProverHint → List (NestedOperations F ProverHint)
  | [] => []
  | .witness m c :: ops => .single (.witness m c) :: toNested ops
  | .assert e :: ops => .single (.assert e) :: toNested ops
  | .lookup l :: ops => .single (.lookup l) :: toNested ops
  | .subcircuit s :: ops => s.ops :: toNested ops

/--
The number of witness variables introduced by these operations.
-/
@[circuit_norm]
def localLength {F : Type} [Field F] {ProverHint : Type} : Operations F ProverHint → ℕ
  | [] => 0
  | .witness m _ :: ops => m + localLength ops
  | .assert _ :: ops => localLength ops
  | .lookup _ :: ops => localLength ops
  | .subcircuit s :: ops => s.localLength + localLength ops

/--
The actual vector of witnesses created by these operations in the given environment.
-/
@[circuit_norm]
def localWitnesses {F : Type} [Field F] {ProverHint : Type}
    (env : Environment F) (hint : ProverHint) :
    (ops : Operations F ProverHint) → Vector F ops.localLength
  | [] => #v[]
  | .witness _ c :: ops => c env hint ++ localWitnesses env hint ops
  | .assert _ :: ops => localWitnesses env hint ops
  | .lookup _ :: ops => localWitnesses env hint ops
  | .subcircuit s :: ops => s.witnesses env hint ++ localWitnesses env hint ops

/-- Induction principle for `Operations`. -/
def induct {F : Type} [Field F] {ProverHint : Type} {motive : Operations F ProverHint → Sort*}
  (empty : motive [])
  (witness : ∀ m c ops, motive ops → motive (.witness m c :: ops))
  (assert : ∀ e ops, motive ops → motive (.assert e :: ops))
  (lookup : ∀ l ops, motive ops → motive (.lookup l :: ops))
  (subcircuit : ∀ {n} (s : Subcircuit F ProverHint n) ops, motive ops → motive (.subcircuit s :: ops))
    (ops : Operations F ProverHint) : motive ops :=
  match ops with
  | [] => empty
  | .witness m c :: ops => witness m c ops (induct empty witness assert lookup subcircuit ops)
  | .assert e :: ops => assert e ops (induct empty witness assert lookup subcircuit ops)
  | .lookup l :: ops => lookup l ops (induct empty witness assert lookup subcircuit ops)
  | .subcircuit s :: ops => subcircuit s ops (induct empty witness assert lookup subcircuit ops)
end Operations

-- generic folding over `Operations` resulting in a proposition

/--
A `Condition` lets you define a predicate on operations, given the type and content of the
current operation as well as the current offset.
-/
structure Condition (F : Type) [Field F] (ProverHint : Type) where
  witness (offset : ℕ) : (m : ℕ) → (Environment F → ProverHint → Vector F m) → Prop := fun _ _ => True
  assert (offset : ℕ) (_ : Expression F) : Prop := True
  lookup (offset : ℕ) (_ : Lookup F) : Prop := True
  subcircuit (offset : ℕ) {m : ℕ} (_ : Subcircuit F ProverHint m) : Prop := True

@[circuit_norm]
def Condition.apply {F : Type} [Field F] {ProverHint : Type}
    (condition : Condition F ProverHint) (offset : ℕ) : Operation F ProverHint → Prop
  | .witness m c => condition.witness offset m c
  | .assert e => condition.assert offset e
  | .lookup l => condition.lookup offset l
  | .subcircuit s => condition.subcircuit offset s

def Condition.implies {F : Type} [Field F] {ProverHint : Type}
    (c c' : Condition F ProverHint) : Condition F ProverHint where
  witness n m compute := c.witness n m compute → c'.witness n m compute
  assert offset e := c.assert offset e → c'.assert offset e
  lookup offset l := c.lookup offset l → c'.lookup offset l
  subcircuit offset _ s := c.subcircuit offset s → c'.subcircuit offset s

namespace Operations
/--
Given a `Condition`, `forAll` is true iff all operations in the list satisfy the condition, at their respective offsets.
The function expects the initial offset as an argument.
-/
 @[circuit_norm]
def forAll {F : Type} [Field F] {ProverHint : Type} (offset : ℕ) (condition : Condition F ProverHint) :
    Operations F ProverHint → Prop
  | [] => True
  | .witness m c :: ops => condition.witness offset m c ∧ forAll (m + offset) condition ops
  | .assert e :: ops => condition.assert offset e ∧ forAll offset condition ops
  | .lookup l :: ops => condition.lookup offset l ∧ forAll offset condition ops
  | .subcircuit s :: ops => condition.subcircuit offset s ∧ forAll (s.localLength + offset) condition ops

/--
Subcircuits start at the same variable offset that the circuit currently is.
In practice, this is always true since subcircuits are instantiated using `subcircuit` or `assertion`.
 -/
@[circuit_norm]
def SubcircuitsConsistent {F : Type} [Field F] {ProverHint : Type}
    (offset : ℕ) (ops : Operations F ProverHint) := ops.forAll offset {
  subcircuit offset {n} _ := n = offset
}

/--
Induction principle for operations _with subcircuit consistency_.

The differences to `induct` are:
- in addition to the operations, we also pass along the initial offset `n`
- in the subcircuit case, the subcircuit offset is the same as the initial offset
-/
def inductConsistent {F : Type} [Field F] {ProverHint : Type}
    {motive : (ops : Operations F ProverHint) → (n : ℕ) → ops.SubcircuitsConsistent n → Sort*}
  (empty : ∀ n, motive [] n trivial)
  (witness : ∀ n m c ops {h}, motive ops (m + n) h →
    motive (.witness m c :: ops) n (by simp_all [SubcircuitsConsistent, forAll]))
  (assert : ∀ n e ops {h}, motive ops n h →
    motive (.assert e :: ops) n (by simp_all [SubcircuitsConsistent, forAll]))
  (lookup : ∀ n l ops {h}, motive ops n h →
    motive (.lookup l :: ops) n (by simp_all [SubcircuitsConsistent, forAll]))
  (subcircuit : ∀ n (s : Subcircuit F ProverHint n) ops {h}, motive ops (s.localLength + n) h →
    motive (.subcircuit s :: ops) n (by simp_all [SubcircuitsConsistent, forAll]))
    (ops : Operations F ProverHint) (n : ℕ) (h : ops.SubcircuitsConsistent n) : motive ops n h :=
  motive' ops n h
where motive' : (ops : Operations F ProverHint) → (n : ℕ) → (h : ops.SubcircuitsConsistent n) → motive ops n h
  | [], n, _ => empty n
  | .witness m c :: ops, n, h | .assert e :: ops, n, h | .lookup e :: ops, n, h => by
    rw [SubcircuitsConsistent, forAll] at h
    first
    | exact witness _ _ _ _ (motive' ops _ h.right)
    | exact assert _ _ _ (motive' ops _ h.right)
    | exact lookup _ _ _ (motive' ops _ h.right)
  | .subcircuit s :: ops, n', h => by
    rename_i n
    rw [SubcircuitsConsistent, forAll] at h
    have n_eq : n = n' := h.left
    subst n_eq
    exact subcircuit n s ops (motive' ops _ h.right)
end Operations

def Condition.ignoreSubcircuit {F : Type} [Field F] {ProverHint : Type}
    (condition : Condition F ProverHint) : Condition F ProverHint :=
  { condition with subcircuit _ _ _ := True }

def Condition.applyFlat {F : Type} [Field F] {ProverHint : Type}
    (condition : Condition F ProverHint) (offset : ℕ) : FlatOperation F ProverHint → Prop
  | .witness m c => condition.witness offset m c
  | .assert e => condition.assert offset e
  | .lookup l => condition.lookup offset l

def FlatOperation.singleLocalLength {F : Type} {ProverHint : Type} : FlatOperation F ProverHint → ℕ
  | .witness m _ => m
  | .assert _ => 0
  | .lookup _ => 0

def FlatOperation.forAll {F : Type} [Field F] {ProverHint : Type}
    (offset : ℕ) (condition : Condition F ProverHint) : List (FlatOperation F ProverHint) → Prop
  | [] => True
  | .witness m c :: ops => condition.witness offset m c ∧ forAll (m + offset) condition ops
  | .assert e :: ops => condition.assert offset e ∧ forAll offset condition ops
  | .lookup l :: ops => condition.lookup offset l ∧ forAll offset condition ops

def Operations.forAllFlat {F : Type} [Field F] {ProverHint : Type}
    (n : ℕ) (condition : Condition F ProverHint) (ops : Operations F ProverHint) : Prop :=
  forAll n { condition with subcircuit n _ s := FlatOperation.forAll n condition s.ops.toFlat } ops
