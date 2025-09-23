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
inductive FlatOperation (sentences : PropertySet F) where
  | witness : (m : ℕ) → (Environment F → Vector F m) → FlatOperation sentences
  | assert : Expression F → FlatOperation sentences
  | lookup : Lookup F → FlatOperation sentences
  | yield : Sentence sentences (Expression F) → FlatOperation sentences
  | use : Sentence sentences (Expression F) → FlatOperation sentences

namespace FlatOperation
instance {sentences : PropertySet F} [Repr F] : Repr (FlatOperation sentences) where
  reprPrec
  | witness m _, _ => "(Witness " ++ reprStr m ++ ")"
  | assert e, _ => "(Assert " ++ reprStr e ++ " == 0)"
  | lookup l, _ => reprStr l
  | yield s, _ => "(Yield " ++ reprStr s ++ ")"
  | use s, _ => "(Use " ++ reprStr s ++ ")"

/--
What it means that "constraints hold" on a list of flat operations:
- For assertions, the expression must evaluate to 0
- For lookups, the evaluated entry must be in the table
- For witness and yield operations, the constraints do not guarantee anything additional
-/
def ConstraintsHoldFlat {sentences : PropertySet F} (eval : Environment F) (yields : YieldContext sentences) (checked : CheckedYields sentences) : List (FlatOperation sentences) → Prop
  | [] => True
  | op :: ops => match op with
    | assert e => (eval e = 0) ∧ ConstraintsHoldFlat eval yields checked ops
    | lookup { table, entry } =>
      table.Contains (entry.map eval) ∧ ConstraintsHoldFlat eval yields checked ops
    | witness _ _ | yield _ => ConstraintsHoldFlat eval yields checked ops
    | use s => s.eval eval ∈ yields.yielded ∧
               (s.eval eval ∈ checked → SentenceHolds (s.eval eval)) ∧
               ConstraintsHoldFlat eval yields checked ops

@[circuit_norm]
def localLength {sentences : PropertySet F} : List (FlatOperation sentences) → ℕ
  | [] => 0
  | witness m _ :: ops => m + localLength ops
  | assert _ :: ops | lookup _ :: ops | yield _ :: ops | use _ :: ops => localLength ops

@[circuit_norm]
def localWitnesses {sentences : PropertySet F} (env : Environment F) : (l : List (FlatOperation sentences)) → Vector F (localLength l)
  | [] => #v[]
  | witness _ compute :: ops => compute env ++ localWitnesses env ops
  | assert _ :: ops | lookup _ :: ops | yield _ :: ops | use _ :: ops => localWitnesses env ops

/-- Collects all yielded sentences from a list of flat operations. -/
def localYields {sentences : PropertySet F} (env : Environment F) : List (FlatOperation sentences) → Set (Sentence sentences F)
  | [] => ∅
  | yield s :: ops => {s.eval env} ∪ localYields env ops
  | witness _ _ :: ops | assert _ :: ops | lookup _ :: ops | use _ :: ops => localYields env ops

@[circuit_norm]
lemma localYields_append {sentences : PropertySet F} (env : Environment F) (ops1 ops2 : List (FlatOperation sentences)) :
    localYields env (ops1 ++ ops2) = localYields env ops1 ∪ localYields env ops2 := by
  induction ops1 with
  | nil => simp [localYields]
  | cons op ops1 ih =>
    cases op with
    | witness m c => simp [localYields, ih]
    | assert e => simp [localYields, ih]
    | lookup l => simp [localYields, ih]
    | yield s =>
        simp only [List.cons_append, localYields, ih, Set.singleton_union]
        aesop
    | use s => simp [localYields, ih]


/-- Induction principle for `FlatOperation`s. -/
def induct {sentences : PropertySet F} {motive : List (FlatOperation sentences) → Sort*}
  (empty : motive [])
  (witness : ∀ m c ops, motive ops → motive (.witness m c :: ops))
  (assert : ∀ e ops, motive ops → motive (.assert e :: ops))
  (lookup : ∀ l ops, motive ops → motive (.lookup l :: ops))
  (yield : ∀ s ops, motive ops → motive (.yield s :: ops))
  (use : ∀ s ops, motive ops → motive (.use s :: ops))
    (ops : List (FlatOperation sentences)) : motive ops :=
  match ops with
  | [] => empty
  | .witness m c :: ops => witness m c ops (induct empty witness assert lookup yield use ops)
  | .assert e :: ops => assert e ops (induct empty witness assert lookup yield use ops)
  | .lookup l :: ops => lookup l ops (induct empty witness assert lookup yield use ops)
  | .yield s :: ops => yield s ops (induct empty witness assert lookup yield use ops)
  | .use s :: ops => use s ops (induct empty witness assert lookup yield use ops)
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
structure Subcircuit (sentences : PropertySet F) (offset : ℕ) where
  ops : List (FlatOperation sentences)

  -- we have a low-level notion of "the constraints hold on these operations".
  -- for convenience, we allow the framework to transform that into custom `Soundness`,
  -- `Completeness` and `UsesLocalWitnessesAndYields` statements (which may involve inputs/outputs, assumptions on inputs, etc)
  Soundness : (env : Environment F) → (yields : YieldContext sentences) → (checkedYields : CheckedYields sentences) → Prop -- usually useful after `checkYields` covers all `use`es in the subcircuit.
  Completeness : Environment F → YieldContext sentences → Prop
  UsesLocalWitnessesAndYields : Environment F → YieldContext sentences → Prop -- SentenceOrder is useful for setting up `Set.univ` to be used as the `checkedYields`

  -- for faster simplification, the subcircuit records its local witness length separately
  -- even though it could be derived from the operations
  localLength : ℕ

  -- `Soundness` needs to follow from the constraints for any witness
  imply_soundness : ∀ (env : Environment F) (yields : YieldContext sentences) (checkedYields : CheckedYields sentences),
    ConstraintsHoldFlat env yields checkedYields ops → Soundness env yields checkedYields

  -- `Completeness` needs to imply the constraints, when using the locally declared witness generators and yields of this circuit
  implied_by_completeness : ∀ (env : Environment F) (yields : YieldContext sentences) (checked : CheckedYields sentences),
    env.ExtendsVector (localWitnesses env ops) offset ∧ FlatOperation.localYields env ops ⊆ yields.yielded →
    Completeness env yields → ConstraintsHoldFlat env yields checked ops

  -- `UsesLocalWitnessesAndYields` needs to follow from the local witness generator condition and yielded sentences
  imply_usesLocalWitnessesAndYields : ∀ (env : Environment F) (yields : YieldContext sentences),
    env.ExtendsVector (localWitnesses env ops) offset ∧ FlatOperation.localYields env ops ⊆ yields.yielded →
    UsesLocalWitnessesAndYields env yields

  -- `localLength` must be consistent with the operations
  localLength_eq : localLength = FlatOperation.localLength ops

@[reducible, circuit_norm]
def Subcircuit.witnesses {sentences : PropertySet F} (sc : Subcircuit sentences n) (env : Environment F) :=
  (FlatOperation.localWitnesses env sc.ops).cast sc.localLength_eq.symm

/--
Core type representing the result of a circuit: a sequence of operations.

In addition to `witness`, `assert` and `lookup`,
`Operation` can also be a `subcircuit`, which itself is essentially a list of operations.
-/
inductive Operation (sentences : PropertySet F) where
  | witness : (m : ℕ) → (compute : Environment F → Vector F m) → Operation sentences
  | assert : Expression F → Operation sentences
  | lookup : Lookup F → Operation sentences
  | yield : Sentence sentences (Expression F) → Operation sentences
  | use : Sentence sentences (Expression F) → Operation sentences
  | subcircuit : {n : ℕ} → Subcircuit sentences n → Operation sentences

namespace Operation
instance {sentences : PropertySet F} [Repr F] : Repr (Operation sentences) where
  reprPrec op _ := match op with
    | witness m _ => "(Witness " ++ reprStr m ++ ")"
    | assert e => "(Assert " ++ reprStr e ++ " == 0)"
    | lookup l => reprStr l
    | yield s => "(Yield " ++ reprStr s ++ ")"
    | use s => "(Use " ++ reprStr s ++ ")"
    | subcircuit { ops, .. } => "(Subcircuit " ++ reprStr ops ++ ")"

/--
The number of witness variables introduced by this operation.
-/
@[circuit_norm]
def localLength {sentences : PropertySet F} : Operation sentences → ℕ
  | .witness m _ => m
  | .assert _ => 0
  | .lookup _ => 0
  | .yield _ => 0
  | .use _ => 0
  | .subcircuit s => s.localLength

def localWitnesses {sentences : PropertySet F} (env : Environment F) : (op : Operation sentences) → Vector F op.localLength
  | .witness _ c => c env
  | .assert _ => #v[]
  | .lookup _ => #v[]
  | .yield _ => #v[]
  | .use _ => #v[]
  | .subcircuit s => s.witnesses env

/-- Collects all yielded sentences from a single operation. -/
def localYields {sentences : PropertySet F} (env : Environment F) : Operation sentences → Set (Sentence sentences F)
  | .yield s => {s.eval env}
  | .witness _ _ | .assert _ | .lookup _ | .use _ => ∅
  | .subcircuit s => FlatOperation.localYields env s.ops
end Operation

/--
`Operations F` is an alias for `List (Operation F sentences)`, so that we can define
methods on operations that take a self argument.
-/
@[reducible, circuit_norm]
def Operations (sentences : PropertySet F) := List (Operation sentences)

namespace Operations
def toList {sentences : PropertySet F} : Operations sentences → List (Operation sentences) := id

/-- move from nested operations back to flat operations -/
def toFlat {sentences : PropertySet F} : Operations sentences → List (FlatOperation sentences)
  | [] => []
  | .witness m c :: ops => .witness m c :: toFlat ops
  | .assert e :: ops => .assert e :: toFlat ops
  | .lookup l :: ops => .lookup l :: toFlat ops
  | .yield s :: ops => .yield s :: toFlat ops
  | .use s :: ops => .use s :: toFlat ops
  | .subcircuit s :: ops => s.ops ++ toFlat ops

/--
The number of witness variables introduced by these operations.
-/
@[circuit_norm]
def localLength {sentences : PropertySet F} : Operations sentences → ℕ
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
def localWitnesses {sentences : PropertySet F} (env : Environment F) : (ops : Operations sentences) → Vector F ops.localLength
  | [] => #v[]
  | .witness _ c :: ops => c env ++ localWitnesses env ops
  | .assert _ :: ops => localWitnesses env ops
  | .lookup _ :: ops => localWitnesses env ops
  | .yield _ :: ops => localWitnesses env ops
  | .use _ :: ops => localWitnesses env ops
  | .subcircuit s :: ops => s.witnesses env ++ localWitnesses env ops

/-- Collects all yielded sentences from a list of operations. -/
def localYields {sentences : PropertySet F} (env : Environment F) : Operations sentences → Set (Sentence sentences F)
  | [] => ∅
  | .yield s :: ops => {s.eval env} ∪ localYields env ops
  | .witness _ _ :: ops | .assert _ :: ops | .lookup _ :: ops | .use _ :: ops => localYields env ops
  | .subcircuit s :: ops => FlatOperation.localYields env s.ops ∪ localYields env ops

@[circuit_norm]
lemma localYields_nil {sentences : PropertySet F} (env : Environment F) :
    localYields env ([] : Operations sentences) = ∅ := rfl

@[circuit_norm]
lemma localYields_cons_subcircuit {sentences : PropertySet F} (env : Environment F) {n : ℕ} (s : Subcircuit sentences n) (ops : Operations sentences) :
    localYields env (.subcircuit s :: ops) = FlatOperation.localYields env s.ops ∪ localYields env ops := rfl

@[circuit_norm]
lemma localYields_cons_witness {sentences : PropertySet F} (env : Environment F) (m : ℕ) (c : Environment F → Vector F m) (ops : Operations sentences) :
    localYields env (.witness m c :: ops) = localYields env ops := rfl

@[circuit_norm]
lemma localYields_cons_assert {sentences : PropertySet F} (env : Environment F) (e : Expression F) (ops : Operations sentences) :
    localYields env (.assert e :: ops) = localYields env ops := rfl

@[circuit_norm]
lemma localYields_cons_lookup {sentences : PropertySet F} (env : Environment F) (l : Lookup F) (ops : Operations sentences) :
    localYields env (.lookup l :: ops) = localYields env ops := rfl

@[circuit_norm]
lemma localYields_cons_yield {sentences : PropertySet F} (env : Environment F) (s : Sentence sentences (Expression F)) (ops : Operations sentences) :
    localYields env (.yield s :: ops) = {s.eval env} ∪ localYields env ops := rfl

@[circuit_norm]
lemma localYields_append {sentences : PropertySet F} (env : Environment F) (ops1 ops2 : Operations sentences) :
    localYields env (ops1 ++ ops2) = localYields env ops1 ∪ localYields env ops2 := by
  induction ops1 with
  | nil => simp [localYields]
  | cons op ops1 ih =>
    cases op with
    | witness m c => simp [localYields, ih]
    | assert e => simp [localYields, ih]
    | lookup l => simp [localYields, ih]
    | yield s =>
      simp only [List.cons_append, localYields, ih]
      ext x
      simp only [Set.mem_singleton_iff, Set.mem_union]
      tauto
    | use s => simp [localYields, ih]
    | subcircuit s => simp [localYields, ih, Set.union_assoc]

/-- Induction principle for `Operations`. -/
def induct {sentences : PropertySet F} {motive : Operations sentences → Sort*}
  (empty : motive [])
  (witness : ∀ m c ops, motive ops → motive (.witness m c :: ops))
  (assert : ∀ e ops, motive ops → motive (.assert e :: ops))
  (lookup : ∀ l ops, motive ops → motive (.lookup l :: ops))
  (yield : ∀ s ops, motive ops → motive (.yield s :: ops))
  (use : ∀ s ops, motive ops → motive (.use s :: ops))
  (subcircuit : ∀ {n} (s : Subcircuit sentences n) ops, motive ops → motive (.subcircuit s :: ops))
    (ops : Operations sentences) : motive ops :=
  match ops with
  | [] => empty
  | .witness m c :: ops => witness m c ops (induct empty witness assert lookup yield use subcircuit ops)
  | .assert e :: ops => assert e ops (induct empty witness assert lookup yield use subcircuit ops)
  | .lookup l :: ops => lookup l ops (induct empty witness assert lookup yield use subcircuit ops)
  | .yield s :: ops => yield s ops (induct empty witness assert lookup yield use subcircuit ops)
  | .use s :: ops => use s ops (induct empty witness assert lookup yield use subcircuit ops)
  | .subcircuit s :: ops => subcircuit s ops (induct empty witness assert lookup yield use subcircuit ops)

/-- The localYields of operations equals the localYields of their flat representation -/
@[circuit_norm]
lemma localYields_toFlat {sentences : PropertySet F} (env : Environment F) (ops : Operations sentences) :
    FlatOperation.localYields env ops.toFlat = Operations.localYields env ops := by
  induction ops using induct with
  | empty => rfl
  | witness m c ops ih => simp [toFlat, FlatOperation.localYields, localYields, ih]
  | assert e ops ih => simp [toFlat, FlatOperation.localYields, localYields, ih]
  | lookup l ops ih => simp [toFlat, FlatOperation.localYields, localYields, ih]
  | yield s ops ih => simp [toFlat, FlatOperation.localYields, localYields, ih]
  | use s ops ih => simp [toFlat, FlatOperation.localYields, localYields, ih]
  | subcircuit s ops ih =>
    simp [toFlat, localYields]
    rw [FlatOperation.localYields_append, ih]

@[circuit_norm]
lemma localYields_flatten {sentences : PropertySet F} (env : Environment F) (opsList : List (Operations sentences)) :
    localYields env opsList.flatten = ⋃ ops ∈ opsList, localYields env ops := by
  induction opsList with
  | nil => simp [localYields]
  | cons ops rest ih =>
    simp [List.flatten, localYields_append, ih]

end Operations

-- generic folding over `Operations` resulting in a proposition

/--
A `Condition` lets you define a predicate on operations, given the type and content of the
current operation as well as the current offset.
-/
structure Condition (sentences : PropertySet F) where
  witness (offset : ℕ) (m : ℕ) (compute : Environment F → Vector F m) : Prop := True
  assert (offset : ℕ) (_ : Expression F) : Prop := True
  lookup (offset : ℕ) (_ : Lookup F) : Prop := True
  yield (offset : ℕ) (_ : Sentence sentences (Expression F)) : Prop := True
  use (offset : ℕ) (_ : Sentence sentences (Expression F)) : Prop := True
  subcircuit (offset : ℕ) {m : ℕ} (_ : Subcircuit sentences m) : Prop := True

@[circuit_norm]
def Condition.apply {sentences : PropertySet F} (condition : Condition sentences) (offset : ℕ) : Operation sentences → Prop
  | .witness m c => condition.witness offset m c
  | .assert e => condition.assert offset e
  | .lookup l => condition.lookup offset l
  | .yield s => condition.yield offset s
  | .use s => condition.use offset s
  | .subcircuit s => condition.subcircuit offset s

def Condition.implies {sentences : PropertySet F} (c c': Condition sentences) : Condition sentences where
  witness n m compute := c.witness n m compute → c'.witness n m compute
  assert offset e := c.assert offset e → c'.assert offset e
  lookup offset l := c.lookup offset l → c'.lookup offset l
  yield offset s := c.yield offset s → c'.yield offset s
  use offset s := c.use offset s → c'.use offset s
  subcircuit offset _ s := c.subcircuit offset s → c'.subcircuit offset s

namespace Operations
/--
Given a `Condition`, `forAll` is true iff all operations in the list satisfy the condition, at their respective offsets.
The function expects the initial offset as an argument.
-/
 @[circuit_norm]
def forAll {sentences : PropertySet F} (offset : ℕ) (condition : Condition sentences) : Operations sentences → Prop
  | [] => True
  | .witness m c :: ops => condition.witness offset m c ∧ forAll (m + offset) condition ops
  | .assert e :: ops => condition.assert offset e ∧ forAll offset condition ops
  | .lookup l :: ops => condition.lookup offset l ∧ forAll offset condition ops
  | .yield s :: ops => condition.yield offset s ∧ forAll offset condition ops
  | .use s :: ops => condition.use offset s ∧ forAll offset condition ops
  | .subcircuit s :: ops => condition.subcircuit offset s ∧ forAll (s.localLength + offset) condition ops

/--
Subcircuits start at the same variable offset that the circuit currently is.
In practice, this is always true since subcircuits are instantiated using `subcircuit` or `assertion`.
 -/
@[circuit_norm]
def SubcircuitsConsistent {sentences : PropertySet F} (offset : ℕ) (ops : Operations sentences) := ops.forAll offset {
  subcircuit offset {n} _ := n = offset
}

/--
Induction principle for operations _with subcircuit consistency_.

The differences to `induct` are:
- in addition to the operations, we also pass along the initial offset `n`
- in the subcircuit case, the subcircuit offset is the same as the initial offset
-/
def inductConsistent {sentences : PropertySet F} {motive : (ops : Operations sentences) → (n : ℕ) → ops.SubcircuitsConsistent n → Sort*}
  (empty : ∀ n, motive [] n trivial)
  (witness : ∀ n m c ops {h}, motive ops (m + n) h →
    motive (.witness m c :: ops) n (by simp_all [SubcircuitsConsistent, forAll]))
  (assert : ∀ n e ops {h}, motive ops n h →
    motive (.assert e :: ops) n (by simp_all [SubcircuitsConsistent, forAll]))
  (lookup : ∀ n l ops {h}, motive ops n h →
    motive (.lookup l :: ops) n (by simp_all [SubcircuitsConsistent, forAll]))
  (yield : ∀ n s ops {h}, motive ops n h →
    motive (.yield s :: ops) n (by simp_all [SubcircuitsConsistent, forAll]))
  (use : ∀ n s ops {h}, motive ops n h →
    motive (.use s :: ops) n (by simp_all [SubcircuitsConsistent, forAll]))
  (subcircuit : ∀ n (s : Subcircuit sentences n) ops {h}, motive ops (s.localLength + n) h →
    motive (.subcircuit s :: ops) n (by simp_all [SubcircuitsConsistent, forAll]))
    (ops : Operations sentences) (n : ℕ) (h : ops.SubcircuitsConsistent n) : motive ops n h :=
  motive' ops n h
where motive' : (ops : Operations sentences) → (n : ℕ) → (h : ops.SubcircuitsConsistent n) → motive ops n h
  | [], n, _ => empty n
  | .witness m c :: ops, n, h | .assert e :: ops, n, h | .lookup e :: ops, n, h | .yield s :: ops, n, h | .use s :: ops, n, h => by
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

def Condition.ignoreSubcircuit {sentences : PropertySet F} (condition : Condition sentences) : Condition sentences :=
  { condition with subcircuit _ _ _ := True }

def Condition.applyFlat {sentences : PropertySet F} (condition : Condition sentences) (offset : ℕ) : FlatOperation sentences → Prop
  | .witness m c => condition.witness offset m c
  | .assert e => condition.assert offset e
  | .lookup l => condition.lookup offset l
  | .yield s => condition.yield offset s
  | .use s => condition.use offset s

def FlatOperation.singleLocalLength {sentences : PropertySet F} : FlatOperation sentences → ℕ
  | .witness m _ => m
  | .assert _ => 0
  | .lookup _ => 0
  | .yield _ => 0
  | .use _ => 0

def FlatOperation.forAll {sentences : PropertySet F} (offset : ℕ) (condition : Condition sentences) : List (FlatOperation sentences) → Prop
  | [] => True
  | .witness m c :: ops => condition.witness offset m c ∧ forAll (m + offset) condition ops
  | .assert e :: ops => condition.assert offset e ∧ forAll offset condition ops
  | .lookup l :: ops => condition.lookup offset l ∧ forAll offset condition ops
  | .yield s :: ops => condition.yield offset s ∧ forAll offset condition ops
  | .use s :: ops => condition.use offset s ∧ forAll offset condition ops

def Operations.forAllFlat {sentences : PropertySet F} (n : ℕ) (condition : Condition sentences) (ops : Operations sentences) : Prop :=
  forAll n { condition with subcircuit n _ s := FlatOperation.forAll n condition s.ops } ops
