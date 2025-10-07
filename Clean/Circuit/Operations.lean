import Clean.Circuit.Expression
import Clean.Circuit.Lookup
import Clean.Circuit.Provable
import Clean.Circuit.SimpGadget

variable {F : Type} [Field F] {α : Type} {n : ℕ}

/--
A named list of field elements, used for yield/use operations.
-/
structure NamedList (F : Type) where
  name : String
  values : List F
deriving DecidableEq, Repr

namespace NamedList
variable [Field F]

/-- Evaluate a NamedList of expressions to a NamedList of field elements -/
def eval (env : Environment F) (nl : NamedList (Expression F)) : NamedList F :=
  { name := nl.name, values := nl.values.map (Expression.eval env) }

end NamedList

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
  | yield : NamedList (Expression F) → FlatOperation F
  | use : NamedList (Expression F) → FlatOperation F

namespace FlatOperation
instance [Repr F] : Repr (FlatOperation F) where
  reprPrec
  | witness m _, _ => "(Witness " ++ reprStr m ++ ")"
  | assert e, _ => "(Assert " ++ reprStr e ++ " == 0)"
  | lookup l, _ => reprStr l
  | yield nl, _ => "(Yield " ++ reprStr nl ++ ")"
  | use nl, _ => "(Use " ++ reprStr nl ++ ")"

/--
What it means that "constraints hold" on a list of flat operations:
- For assertions, the expression must evaluate to 0
- For lookups, the evaluated entry must be in the table
-/
def ConstraintsHoldFlat (eval : Environment F) (yielded : Set (NamedList F)) : List (FlatOperation F) → Prop
  | [] => True
  | op :: ops => match op with
    | assert e => (eval e = 0) ∧ ConstraintsHoldFlat eval yielded ops
    | lookup { table, entry } =>
      table.Contains (entry.map eval) ∧ ConstraintsHoldFlat eval yielded ops
    | use nl => nl.eval eval ∈ yielded ∧ ConstraintsHoldFlat eval yielded ops
    | _ => ConstraintsHoldFlat eval yielded ops

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

def localYields (env : Environment F) : List (FlatOperation F) → Set (NamedList F)
  | [] => ∅
  | witness _ _ :: ops => localYields env ops
  | assert _ :: ops => localYields env ops
  | lookup _ :: ops => localYields env ops
  | yield nl :: ops => {nl.eval env} ∪ localYields env ops
  | use _ :: ops => localYields env ops

/-- Induction principle for `FlatOperation`s. -/
def induct {motive : List (FlatOperation F) → Sort*}
  (empty : motive [])
  (witness : ∀ m c ops, motive ops → motive (.witness m c :: ops))
  (assert : ∀ e ops, motive ops → motive (.assert e :: ops))
  (lookup : ∀ l ops, motive ops → motive (.lookup l :: ops))
  (yield : ∀ nl ops, motive ops → motive (.yield nl :: ops))
  (use : ∀ nl ops, motive ops → motive (.use nl :: ops))
    (ops : List (FlatOperation F)) : motive ops :=
  match ops with
  | [] => empty
  | .witness m c :: ops => witness m c ops (induct empty witness assert lookup yield use ops)
  | .assert e :: ops => assert e ops (induct empty witness assert lookup yield use ops)
  | .lookup l :: ops => lookup l ops (induct empty witness assert lookup yield use ops)
  | .yield nl :: ops => yield nl ops (induct empty witness assert lookup yield use ops)
  | .use nl :: ops => use nl ops (induct empty witness assert lookup yield use ops)
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
  Soundness : Environment F → Set (NamedList F) → Prop
  Completeness : Environment F → Set (NamedList F) → Prop
  UsesLocalWitnesses : Environment F → Set (NamedList F) → Prop

  -- for faster simplification, the subcircuit records its local witness length separately
  -- even though it could be derived from the operations
  localLength : ℕ

  -- `Soundness` needs to follow from the constraints for any witness
  imply_soundness : ∀ env yielded,
    ConstraintsHoldFlat env yielded ops → Soundness env yielded

  -- `Completeness` needs to imply the constraints, when using the locally declared witness generators of this circuit
  implied_by_completeness : ∀ env yielded,
    env.ExtendsVector (localWitnesses env ops) offset →
    FlatOperation.localYields env ops ⊆ yielded →
    Completeness env yielded → ConstraintsHoldFlat env yielded ops

  -- `UsesLocalWitnesses` needs to follow from the local witness generator condition
  imply_usesLocalWitnesses : ∀ env yielded,
    env.ExtendsVector (localWitnesses env ops) offset →
    FlatOperation.localYields env ops ⊆ yielded →
    UsesLocalWitnesses env yielded

  -- `localLength` must be consistent with the operations
  localLength_eq : localLength = FlatOperation.localLength ops

@[reducible, circuit_norm]
def Subcircuit.witnesses (sc : Subcircuit F n) env :=
  (FlatOperation.localWitnesses env sc.ops).cast sc.localLength_eq.symm

/--
Core type representing the result of a circuit: a sequence of operations.

In addition to `witness`, `assert` and `lookup`,
`Operation` can also be a `subcircuit`, which itself is essentially a list of operations,
or `yield`/`use` operations for passing verified values between circuits.
-/
inductive Operation (F : Type) [Field F] where
  | witness : (m : ℕ) → (compute : Environment F → Vector F m) → Operation F
  | assert : Expression F → Operation F
  | lookup : Lookup F → Operation F
  | subcircuit : {n : ℕ} → Subcircuit F n → Operation F
  | yield : NamedList (Expression F) → Operation F
  | use : NamedList (Expression F) → Operation F

namespace Operation
instance [Repr F] : Repr (Operation F) where
  reprPrec op _ := match op with
    | witness m _ => "(Witness " ++ reprStr m ++ ")"
    | assert e => "(Assert " ++ reprStr e ++ " == 0)"
    | lookup l => reprStr l
    | subcircuit { ops, .. } => "(Subcircuit " ++ reprStr ops ++ ")"
    | yield nl => "(Yield " ++ reprStr nl ++ ")"
    | use nl => "(Use " ++ reprStr nl ++ ")"

/--
The number of witness variables introduced by this operation.
-/
@[circuit_norm]
def localLength : Operation F → ℕ
  | .witness m _ => m
  | .assert _ => 0
  | .lookup _ => 0
  | .subcircuit s => s.localLength
  | .yield _ => 0
  | .use _ => 0

def localWitnesses (env : Environment F) : (op : Operation F) → Vector F op.localLength
  | .witness _ c => c env
  | .assert _ => #v[]
  | .lookup _ => #v[]
  | .subcircuit s => s.witnesses env
  | .yield _ => #v[]
  | .use _ => #v[]
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
  | .subcircuit s :: ops => s.ops ++ toFlat ops
  | .yield nl :: ops => .yield nl :: toFlat ops
  | .use nl :: ops => .use nl :: toFlat ops

/--
The number of witness variables introduced by these operations.
-/
@[circuit_norm]
def localLength : Operations F → ℕ
  | [] => 0
  | .witness m _ :: ops => m + localLength ops
  | .assert _ :: ops => localLength ops
  | .lookup _ :: ops => localLength ops
  | .subcircuit s :: ops => s.localLength + localLength ops
  | .yield _ :: ops => localLength ops
  | .use _ :: ops => localLength ops

/--
The actual vector of witnesses created by these operations in the given environment.
-/
@[circuit_norm]
def localWitnesses (env : Environment F) : (ops : Operations F) → Vector F ops.localLength
  | [] => #v[]
  | .witness _ c :: ops => c env ++ localWitnesses env ops
  | .assert _ :: ops => localWitnesses env ops
  | .lookup _ :: ops => localWitnesses env ops
  | .subcircuit s :: ops => s.witnesses env ++ localWitnesses env ops
  | .yield _ :: ops => localWitnesses env ops
  | .use _ :: ops => localWitnesses env ops

@[circuit_norm]
def localYields (env : Environment F) : Operations F → Set (NamedList F)
  | [] => ∅
  | .witness _ _ :: ops => localYields env ops
  | .assert _ :: ops => localYields env ops
  | .lookup _ :: ops => localYields env ops
  | .yield nl :: ops => {nl.eval env} ∪ localYields env ops
  | .use _ :: ops => localYields env ops
  | .subcircuit _ :: ops => localYields env ops  -- subcircuits don't yield to parent

@[circuit_norm]
theorem localYields_append (env : Environment F) (ops1 ops2 : Operations F) :
    localYields env (ops1 ++ ops2) = localYields env ops1 ∪ localYields env ops2 := by
  induction ops1 with
  | nil => simp [localYields]
  | cons op ops1 ih =>
    cases op <;> simp [localYields, ih]
    case yield nl =>
      rw [Set.insert_union]

@[circuit_norm]
theorem localYields_flatten (env : Environment F) (opss : List (Operations F)) :
    localYields env (List.flatten opss) = ⋃ ops ∈ opss, localYields env ops := by
  induction opss with
  | nil => simp [localYields]
  | cons ops opss ih =>
    simp [List.flatten, localYields_append, ih]

/-- Induction principle for `Operations`. -/
def induct {motive : Operations F → Sort*}
  (empty : motive [])
  (witness : ∀ m c ops, motive ops → motive (.witness m c :: ops))
  (assert : ∀ e ops, motive ops → motive (.assert e :: ops))
  (lookup : ∀ l ops, motive ops → motive (.lookup l :: ops))
  (subcircuit : ∀ {n} (s : Subcircuit F n) ops, motive ops → motive (.subcircuit s :: ops))
  (yield : ∀ nl ops, motive ops → motive (.yield nl :: ops))
  (use : ∀ nl ops, motive ops → motive (.use nl :: ops))
    (ops : Operations F) : motive ops :=
  match ops with
  | [] => empty
  | .witness m c :: ops => witness m c ops (induct empty witness assert lookup subcircuit yield use ops)
  | .assert e :: ops => assert e ops (induct empty witness assert lookup subcircuit yield use ops)
  | .lookup l :: ops => lookup l ops (induct empty witness assert lookup subcircuit yield use ops)
  | .subcircuit s :: ops => subcircuit s ops (induct empty witness assert lookup subcircuit yield use ops)
  | .yield nl :: ops => yield nl ops (induct empty witness assert lookup subcircuit yield use ops)
  | .use nl :: ops => use nl ops (induct empty witness assert lookup subcircuit yield use ops)
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
  subcircuit (offset : ℕ) {m : ℕ} (_ : Subcircuit F m) : Prop := True
  yield (offset : ℕ) (_ : NamedList (Expression F)) : Prop := True
  use (offset : ℕ) (_ : NamedList (Expression F)) : Prop := True

@[circuit_norm]
def Condition.apply (condition : Condition F) (offset : ℕ) : Operation F → Prop
  | .witness m c => condition.witness offset m c
  | .assert e => condition.assert offset e
  | .lookup l => condition.lookup offset l
  | .subcircuit s => condition.subcircuit offset s
  | .yield nl => condition.yield offset nl
  | .use nl => condition.use offset nl

def Condition.implies (c c': Condition F) : Condition F where
  witness n m compute := c.witness n m compute → c'.witness n m compute
  assert offset e := c.assert offset e → c'.assert offset e
  lookup offset l := c.lookup offset l → c'.lookup offset l
  subcircuit offset _ s := c.subcircuit offset s → c'.subcircuit offset s
  yield offset nl := c.yield offset nl → c'.yield offset nl
  use offset nl := c.use offset nl → c'.use offset nl

def Condition.isTrue {F : Type} [Field F] (c : Condition F) :=
  (∀ n m compute, c.witness n m compute) ∧
  (∀ n e, c.assert n e) ∧
  (∀ n l, c.lookup n l) ∧
  (∀ n nl, c.yield n nl) ∧
  (∀ n nl, c.use n nl) ∧
  (∀ n {m} s, c.subcircuit n (m := m) s)

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
  | .subcircuit s :: ops => condition.subcircuit offset s ∧ forAll (s.localLength + offset) condition ops
  | .yield nl :: ops => condition.yield offset nl ∧ forAll offset condition ops
  | .use nl :: ops => condition.use offset nl ∧ forAll offset condition ops

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
  (subcircuit : ∀ n (s : Subcircuit F n) ops {h}, motive ops (s.localLength + n) h →
    motive (.subcircuit s :: ops) n (by simp_all [SubcircuitsConsistent, forAll]))
  (yield : ∀ n nl ops {h}, motive ops n h →
    motive (.yield nl :: ops) n (by simp_all [SubcircuitsConsistent, forAll]))
  (use : ∀ n nl ops {h}, motive ops n h →
    motive (.use nl :: ops) n (by simp_all [SubcircuitsConsistent, forAll]))
    (ops : Operations F) (n : ℕ) (h : ops.SubcircuitsConsistent n) : motive ops n h :=
  motive' ops n h
where motive' : (ops : Operations F) → (n : ℕ) → (h : ops.SubcircuitsConsistent n) → motive ops n h
  | [], n, _ => empty n
  | .witness m c :: ops, n, h | .assert e :: ops, n, h | .lookup e :: ops, n, h | .yield _ :: ops, n, h | .use _ :: ops, n, h => by
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
  | .yield nl => condition.yield offset nl
  | .use nl => condition.use offset nl

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
  | .yield nl :: ops => condition.yield offset nl ∧ forAll offset condition ops
  | .use nl :: ops => condition.use offset nl ∧ forAll offset condition ops

def Operations.forAllFlat (n : ℕ) (condition : Condition F) (ops : Operations F) : Prop :=
  forAll n { condition with subcircuit n _ s := FlatOperation.forAll n condition s.ops } ops
