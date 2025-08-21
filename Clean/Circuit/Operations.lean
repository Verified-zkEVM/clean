import Clean.Circuit.Expression
import Clean.Circuit.Lookup
import Clean.Circuit.PropertyLookup
import Clean.Circuit.Provable
import Clean.Circuit.SimpGadget

variable {F : Type} [Field F] {α : Type} {n : ℕ}

/--
`FlatOperation` models the operations that can be done in a circuit, in a simple/flat way.

This is an intermediary type on the way to defining the full inductive `Operation` type.
It is needed because we already need to talk about operations in the `Subcircuit` definition,
which in turn is needed to define `Operation`.
-/
inductive FlatOperation (F : Type) where
  | witness : (m : ℕ) → (Environment F → Vector F m) → FlatOperation F
  | assert : Expression F → FlatOperation F
  | lookup : Lookup F → FlatOperation F
  | yield : TupleProperty F → FlatOperation F
  | use : TupleProperty F → FlatOperation F

namespace FlatOperation
instance [Repr F] : Repr (FlatOperation F) where
  reprPrec
  | witness m _, _ => "(Witness " ++ reprStr m ++ ")"
  | assert e, _ => "(Assert " ++ reprStr e ++ " == 0)"
  | lookup l, _ => reprStr l
  | yield tp, _ => "(Yield " ++ reprStr tp ++ ")"
  | use tp, _ => "(Use " ++ reprStr tp ++ ")"

/--
What it means that "constraints hold" on a list of flat operations:
- For assertions, the expression must evaluate to 0
- For lookups, the evaluated entry must be in the table
-/
def ConstraintsHoldFlat (eval : Environment F) : List (FlatOperation F) → Prop
  | [] => True
  | op :: ops => match op with
    | assert e => (eval e = 0) ∧ ConstraintsHoldFlat eval ops
    | lookup { table, entry } =>
      table.Contains (entry.map eval) ∧ ConstraintsHoldFlat eval ops
    -- The backend is supposed to make sure, for every `use tp`, there's `yield tp` somewhere.
    -- That's not stated here because it's a global property to be checked for the combination of all circuits & tables.
    | _ => ConstraintsHoldFlat eval ops

@[circuit_norm]
def localLength : List (FlatOperation F) → ℕ
  | [] => 0
  | witness m _ :: ops => m + localLength ops
  | assert _ :: ops | lookup _ :: ops | yield _ :: ops | use _ :: ops => localLength ops

@[circuit_norm]
def localWitnesses (env : Environment F) : (l : List (FlatOperation F)) → Vector F (localLength l)
  | [] => #v[]
  | witness _ compute :: ops => compute env ++ localWitnesses env ops
  | assert _ :: ops | lookup _ :: ops | yield _ :: ops | use _ :: ops => localWitnesses env ops

/-- Induction principle for `FlatOperation`s. -/
def induct {motive : List (FlatOperation F) → Sort*}
  (empty : motive [])
  (witness : ∀ m c ops, motive ops → motive (.witness m c :: ops))
  (assert : ∀ e ops, motive ops → motive (.assert e :: ops))
  (lookup : ∀ l ops, motive ops → motive (.lookup l :: ops))
  (yield : ∀ tp ops, motive ops → motive (.yield tp :: ops))
  (use : ∀ tp ops, motive ops → motive (.use tp :: ops))
    (ops : List (FlatOperation F)) : motive ops :=
  match ops with
  | [] => empty
  | .witness m c :: ops => witness m c ops (induct empty witness assert lookup yield use ops)
  | .assert e :: ops => assert e ops (induct empty witness assert lookup yield use ops)
  | .lookup l :: ops => lookup l ops (induct empty witness assert lookup yield use ops)
  | .yield tp :: ops => yield tp ops (induct empty witness assert lookup yield use ops)
  | .use tp :: ops => use tp ops (induct empty witness assert lookup yield use ops)
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
structure Subcircuit (F : Type) [Field F] (offset : ℕ) where
  ops : List (FlatOperation F)

  -- we have a low-level notion of "the constraints hold on these operations".
  -- for convenience, we allow the framework to transform that into custom `Soundness`,
  -- `Completeness` and `UsesLocalWitnesses` statements (which may involve inputs/outputs, assumptions on inputs, etc)
  Soundness : Environment F → Prop
  Completeness : Environment F → Prop
  UsesLocalWitnesses : Environment F → Prop

  -- for faster simplification, the subcircuit records its local witness length separately
  -- even though it could be derived from the operations
  localLength : ℕ

  -- `Soundness` needs to follow from the constraints for any witness
  imply_soundness : ∀ env,
    ConstraintsHoldFlat env ops → Soundness env

  -- `Completeness` needs to imply the constraints, when using the locally declared witness generators of this circuit
  implied_by_completeness : ∀ env, env.ExtendsVector (localWitnesses env ops) offset →
    Completeness env → ConstraintsHoldFlat env ops

  -- `UsesLocalWitnesses` needs to follow from the local witness generator condition
  imply_usesLocalWitnesses : ∀ env, env.ExtendsVector (localWitnesses env ops) offset →
    UsesLocalWitnesses env

  -- `localLength` must be consistent with the operations
  localLength_eq : localLength = FlatOperation.localLength ops

@[reducible, circuit_norm]
def Subcircuit.witnesses (sc : Subcircuit F n) env :=
  (FlatOperation.localWitnesses env sc.ops).cast sc.localLength_eq.symm

/--
Core type representing the result of a circuit: a sequence of operations.

In addition to `witness`, `assert`, `lookup`, `yield` and `use`,
`Operation` can also be a `subcircuit`, which itself is essentially a list of operations.
-/
inductive Operation (F : Type) [Field F] where
  | witness : (m : ℕ) → (compute : Environment F → Vector F m) → Operation F
  | assert : Expression F → Operation F
  | lookup : Lookup F → Operation F
  | yield : TupleProperty F → Operation F
  | use : TupleProperty F → Operation F
  | subcircuit : {n : ℕ} → Subcircuit F n → Operation F

namespace Operation
instance [Repr F] : Repr (Operation F) where
  reprPrec op _ := match op with
    | witness m _ => "(Witness " ++ reprStr m ++ ")"
    | assert e => "(Assert " ++ reprStr e ++ " == 0)"
    | lookup l => reprStr l
    | yield tp => "(Yield " ++ reprStr tp ++ ")"
    | use tp => "(Use " ++ reprStr tp ++ ")"
    | subcircuit { ops, .. } => "(Subcircuit " ++ reprStr ops ++ ")"

/--
The number of witness variables introduced by this operation.
-/
@[circuit_norm]
def localLength : Operation F → ℕ
  | .witness m _ => m
  | .assert _ => 0
  | .lookup _ => 0
  | .yield _ => 0
  | .use _ => 0
  | .subcircuit s => s.localLength

def localWitnesses (env : Environment F) : (op : Operation F) → Vector F op.localLength
  | .witness _ c => c env
  | .assert _ => #v[]
  | .lookup _ => #v[]
  | .yield _ => #v[]
  | .use _ => #v[]
  | .subcircuit s => s.witnesses env
end Operation

/--
`Operations F` is an alias for `List (Operation F)`, so that we can define
methods on operations that take a self argument.
-/
@[reducible, circuit_norm]
def Operations (F : Type) [Field F] := List (Operation F)

namespace Operations
def toList : Operations F → List (Operation F) := id

/-- move from nested operations back to flat operations -/
def toFlat : Operations F → List (FlatOperation F)
  | [] => []
  | .witness m c :: ops => .witness m c :: toFlat ops
  | .assert e :: ops => .assert e :: toFlat ops
  | .lookup l :: ops => .lookup l :: toFlat ops
  | .yield tp :: ops => .yield tp :: toFlat ops
  | .use tp :: ops => .use tp :: toFlat ops
  | .subcircuit s :: ops => s.ops ++ toFlat ops

/--
The number of witness variables introduced by these operations.
-/
@[circuit_norm]
def localLength : Operations F → ℕ
  | [] => 0
  | .witness m _ :: ops => m + localLength ops
  | .assert _ :: ops => localLength ops
  | .lookup _ :: ops => localLength ops
  | .yield _ :: ops => localLength ops
  | .use _ :: ops => localLength ops
  | .subcircuit s :: ops => s.localLength + localLength ops

/--
The actual vector of witnesses created by these operations in the given environment.
-/
@[circuit_norm]
def localWitnesses (env : Environment F) : (ops : Operations F) → Vector F ops.localLength
  | [] => #v[]
  | .witness _ c :: ops => c env ++ localWitnesses env ops
  | .assert _ :: ops => localWitnesses env ops
  | .lookup _ :: ops => localWitnesses env ops
  | .yield _ :: ops => localWitnesses env ops
  | .use _ :: ops => localWitnesses env ops
  | .subcircuit s :: ops => s.witnesses env ++ localWitnesses env ops

/-- Induction principle for `Operations`. -/
def induct {motive : Operations F → Sort*}
  (empty : motive [])
  (witness : ∀ m c ops, motive ops → motive (.witness m c :: ops))
  (assert : ∀ e ops, motive ops → motive (.assert e :: ops))
  (lookup : ∀ l ops, motive ops → motive (.lookup l :: ops))
  (yield : ∀ tp ops, motive ops → motive (.yield tp :: ops))
  (use : ∀ tp ops, motive ops → motive (.use tp :: ops))
  (subcircuit : ∀ {n} (s : Subcircuit F n) ops, motive ops → motive (.subcircuit s :: ops))
    (ops : Operations F) : motive ops :=
  match ops with
  | [] => empty
  | .witness m c :: ops => witness m c ops (induct empty witness assert lookup yield use subcircuit ops)
  | .assert e :: ops => assert e ops (induct empty witness assert lookup yield use subcircuit ops)
  | .lookup l :: ops => lookup l ops (induct empty witness assert lookup yield use subcircuit ops)
  | .yield tp :: ops => yield tp ops (induct empty witness assert lookup yield use subcircuit ops)
  | .use tp :: ops => use tp ops (induct empty witness assert lookup yield use subcircuit ops)
  | .subcircuit s :: ops => subcircuit s ops (induct empty witness assert lookup yield use subcircuit ops)
end Operations

-- generic folding over `Operations` resulting in a proposition

/--
A `Condition` lets you define a predicate on operations, given the type and content of the
current operation as well as the current offset.
-/
structure Condition (F : Type) [Field F] where
  witness (offset : ℕ) : (m : ℕ) → (Environment F → Vector F m) → Prop := fun _ _ => True
  assert (offset : ℕ) (_ : Expression F) : Prop := True
  lookup (offset : ℕ) (_ : Lookup F) : Prop := True
  yield (offset : ℕ) (_ : TupleProperty F) : Prop := True
  use (offset : ℕ) (_ : TupleProperty F) : Prop := True
  subcircuit (offset : ℕ) {m : ℕ} (_ : Subcircuit F m) : Prop := True

@[circuit_norm]
def Condition.apply (condition : Condition F) (offset : ℕ) : Operation F → Prop
  | .witness m c => condition.witness offset m c
  | .assert e => condition.assert offset e
  | .lookup l => condition.lookup offset l
  | .yield tp => condition.yield offset tp
  | .use tp => condition.use offset tp
  | .subcircuit s => condition.subcircuit offset s

def Condition.implies (c c': Condition F) : Condition F where
  witness n m compute := c.witness n m compute → c'.witness n m compute
  assert offset e := c.assert offset e → c'.assert offset e
  lookup offset l := c.lookup offset l → c'.lookup offset l
  yield offset tp := c.yield offset tp → c'.yield offset tp
  use offset tp := c.use offset tp → c'.use offset tp
  subcircuit offset _ s := c.subcircuit offset s → c'.subcircuit offset s

namespace Operations
/--
Given a `Condition`, `forAll` is true iff all operations in the list satisfy the condition, at their respective offsets.
The function expects the initial offset as an argument.
-/
 @[circuit_norm]
def forAll (offset : ℕ) (condition : Condition F) : Operations F → Prop
  | [] => True
  | .witness m c :: ops => condition.witness offset m c ∧ forAll (m + offset) condition ops
  | .assert e :: ops => condition.assert offset e ∧ forAll offset condition ops
  | .lookup l :: ops => condition.lookup offset l ∧ forAll offset condition ops
  | .yield tp :: ops => condition.yield offset tp ∧ forAll offset condition ops
  | .use tp :: ops => condition.use offset tp ∧ forAll offset condition ops
  | .subcircuit s :: ops => condition.subcircuit offset s ∧ forAll (s.localLength + offset) condition ops

/--
Subcircuits start at the same variable offset that the circuit currently is.
In practice, this is always true since subcircuits are instantiated using `subcircuit` or `assertion`.
 -/
@[circuit_norm]
def SubcircuitsConsistent (offset : ℕ) (ops : Operations F) := ops.forAll offset {
  subcircuit offset {n} _ := n = offset
}

/--
Induction principle for operations _with subcircuit consistency_.

The differences to `induct` are:
- in addition to the operations, we also pass along the initial offset `n`
- in the subcircuit case, the subcircuit offset is the same as the initial offset
-/
def inductConsistent {motive : (ops : Operations F) → (n : ℕ) → ops.SubcircuitsConsistent n → Sort*}
  (empty : ∀ n, motive [] n trivial)
  (witness : ∀ n m c ops {h}, motive ops (m + n) h →
    motive (.witness m c :: ops) n (by simp_all [SubcircuitsConsistent, forAll]))
  (assert : ∀ n e ops {h}, motive ops n h →
    motive (.assert e :: ops) n (by simp_all [SubcircuitsConsistent, forAll]))
  (lookup : ∀ n l ops {h}, motive ops n h →
    motive (.lookup l :: ops) n (by simp_all [SubcircuitsConsistent, forAll]))
  (yield : ∀ n tp ops {h}, motive ops n h →
    motive (.yield tp ::ops) n (by simp_all [SubcircuitsConsistent, forAll]))
  (use : ∀ n tp ops {h}, motive ops n h →
    motive (.use tp :: ops) n (by simp_all [SubcircuitsConsistent, forAll]))
  (subcircuit : ∀ n (s : Subcircuit F n) ops {h}, motive ops (s.localLength + n) h →
    motive (.subcircuit s :: ops) n (by simp_all [SubcircuitsConsistent, forAll]))
    (ops : Operations F) (n : ℕ) (h : ops.SubcircuitsConsistent n) : motive ops n h :=
  motive' ops n h
where motive' : (ops : Operations F) → (n : ℕ) → (h : ops.SubcircuitsConsistent n) → motive ops n h
  | [], n, _ => empty n
  | .witness m c :: ops, n, h | .assert e :: ops, n, h | .lookup e :: ops, n, h | .yield tp :: ops, n, h | .use tp ::ops, n, h => by
    rw [SubcircuitsConsistent, forAll] at h
    first
    | exact witness _ _ _ _ (motive' ops _ h.right)
    | exact assert _ _ _ (motive' ops _ h.right)
    | exact lookup _ _ _ (motive' ops _ h.right)
    | exact yield _ _ _ (motive' ops _ h.right)
    | exact use _ _ _ (motive' ops _ h.right)
  | .subcircuit s :: ops, n', h => by
    rename_i n
    rw [SubcircuitsConsistent, forAll] at h
    have n_eq : n = n' := h.left
    subst n_eq
    exact subcircuit n s ops (motive' ops _ h.right)
end Operations

def Condition.ignoreSubcircuit (condition : Condition F) : Condition F :=
  { condition with subcircuit _ _ _ := True }

def Condition.applyFlat (condition : Condition F) (offset : ℕ) : FlatOperation F → Prop
  | .witness m c => condition.witness offset m c
  | .assert e => condition.assert offset e
  | .lookup l => condition.lookup offset l
  | .yield tp => condition.yield offset tp
  | .use tp => condition.use offset tp

def FlatOperation.singleLocalLength : FlatOperation F → ℕ
  | .witness m _ => m
  | .assert _ => 0
  | .lookup _ => 0
  | .yield _ => 0
  | .use _ => 0

def FlatOperation.forAll (offset : ℕ) (condition : Condition F) : List (FlatOperation F) → Prop
  | [] => True
  | .witness m c :: ops => condition.witness offset m c ∧ forAll (m + offset) condition ops
  | .assert e :: ops => condition.assert offset e ∧ forAll offset condition ops
  | .lookup l :: ops => condition.lookup offset l ∧ forAll offset condition ops
  | .yield tp :: ops => condition.yield offset tp ∧ forAll offset condition ops
  | .use tp :: ops => condition.use offset tp ∧ forAll offset condition ops

def Operations.forAllFlat (n : ℕ) (condition : Condition F) (ops : Operations F) : Prop :=
  forAll n { condition with subcircuit n _ s := FlatOperation.forAll n condition s.ops } ops
