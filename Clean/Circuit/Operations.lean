import Clean.Circuit.Expression
import Clean.Circuit.Lookup
import Clean.Circuit.Provable
import Clean.Circuit.SimpGadget
import Mathlib.Data.Finsupp.Defs

variable {F : Type} [Field F] {α : Type} {n : ℕ}

/--
A named list of field elements, used for multiset add operations.
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
An `InteractionDelta` represents a change to an interaction (multiset argument), as a list
of (NamedList, multiplicity) pairs. This representation is computable and supports efficient
addition via list concatenation. Two deltas are semantically equal if they have the same
total multiplicity for each key (checked via `toFinsupp` in proofs).

Note: Multiplicities are in `F` (the field) rather than `ℤ` because the `enabled` flag used
in conditional emission (e.g., `emitStateWhen enabled mult state`) is a field element.
Using `F` avoids ambiguity in converting `F → ℤ` and allows direct multiplication
`enabled * mult` without coercion issues.
-/
abbrev InteractionDelta (F : Type) := List (NamedList F × F)

namespace InteractionDelta
variable {F : Type}

instance : Zero (InteractionDelta F) := ⟨[]⟩

instance : Inhabited (InteractionDelta F) := ⟨0⟩

/-- Create a singleton interaction delta with one named list and its multiplicity -/
def single (nl : NamedList F) (mult : F) : InteractionDelta F :=
  [(nl, mult)]

/-- Addition is list concatenation - semantic equality handles combining multiplicities -/
instance : Add (InteractionDelta F) := ⟨List.append⟩

/-- Negation: negate all multiplicities -/
def neg [Neg F] (d : InteractionDelta F) : InteractionDelta F :=
  d.map (fun (nl, m) => (nl, -m))

instance [Neg F] : Neg (InteractionDelta F) := ⟨neg⟩

variable [Field F]

/-- Get the total multiplicity for a key by summing all entries -/
def getMultiplicity [DecidableEq F] (nl : NamedList F) (d : InteractionDelta F) : F :=
  d.foldl (fun acc (k, v) => if k = nl then acc + v else acc) 0

/-- Convert to Finsupp for proofs (noncomputable) -/
noncomputable def toFinsupp [DecidableEq F] (d : InteractionDelta F) : Finsupp (NamedList F) F :=
  d.foldl (fun acc (nl, m) => acc + Finsupp.single nl m) 0

omit [Field F] in
@[circuit_norm] theorem add_eq_append (d1 d2 : InteractionDelta F) : d1 + d2 = d1 ++ d2 := rfl

omit [Field F] in
@[circuit_norm] theorem zero_eq_nil : (0 : InteractionDelta F) = [] := rfl

omit [Field F] in
@[circuit_norm] theorem add_zero' (d : InteractionDelta F) : d + 0 = d := List.append_nil d

omit [Field F] in
@[circuit_norm] theorem zero_add' (d : InteractionDelta F) : 0 + d = d := List.nil_append d

omit [Field F] in
theorem add_assoc' (d1 d2 d3 : InteractionDelta F) : (d1 + d2) + d3 = d1 + (d2 + d3) :=
  List.append_assoc d1 d2 d3

/-- AddMonoid instance for InteractionDelta.
    Note: Addition is list concatenation, so commutativity only holds semantically
    (same result via toFinsupp), not definitionally. -/
instance instAddMonoid : AddMonoid (InteractionDelta F) where
  add := (· + ·)
  add_assoc := add_assoc'
  zero := 0
  zero_add := zero_add'
  add_zero := add_zero'
  nsmul := nsmulRec

@[circuit_norm]
theorem single_zero (nl : NamedList F) : single nl 0 = [(nl, 0)] := rfl

-- Semantic equality: two deltas are equal if they have the same toFinsupp
theorem toFinsupp_add [DecidableEq F] (d1 d2 : InteractionDelta F) :
    (d1 + d2).toFinsupp = d1.toFinsupp + d2.toFinsupp := by
  simp only [toFinsupp, add_eq_append]
  have h : ∀ (init : Finsupp (NamedList F) F) (l : List (NamedList F × F)),
      List.foldl (fun acc x => acc + Finsupp.single x.1 x.2) init l =
      init + List.foldl (fun acc x => acc + Finsupp.single x.1 x.2) 0 l := by
    intro init l
    induction l generalizing init with
    | nil => simp
    | cons hd' tl' ih' =>
      simp only [List.foldl_cons]
      rw [ih' (init + Finsupp.single hd'.1 hd'.2), ih' (0 + Finsupp.single hd'.1 hd'.2)]
      simp only [zero_add]
      rw [add_assoc]
  induction d1 with
  | nil => simp [List.foldl_nil]
  | cons hd tl ih =>
    simp only [List.cons_append, List.foldl_cons]
    rw [h (0 + Finsupp.single hd.1 hd.2) (tl ++ d2)]
    simp only [zero_add]
    rw [ih]
    rw [h (Finsupp.single hd.1 hd.2) tl]
    rw [add_assoc]

theorem toFinsupp_single [DecidableEq F] (nl : NamedList F) (m : F) :
    (single nl m).toFinsupp = Finsupp.single nl m := by
  simp only [single, toFinsupp, List.foldl_cons, List.foldl_nil, zero_add]

theorem toFinsupp_zero [DecidableEq F] : toFinsupp (0 : InteractionDelta F) = 0 := by
  simp only [zero_eq_nil, toFinsupp, List.foldl_nil]

theorem toFinsupp_zero_mult [DecidableEq F] (nl1 nl2 : NamedList F) :
    toFinsupp ([(nl1, 0), (nl2, 0)] : InteractionDelta F) = 0 := by
  simp only [toFinsupp, List.foldl_cons, List.foldl_nil, Finsupp.single_zero, add_zero]

/-- Helper lemma: equality of InteractionDeltas implies equality of their toFinsupp. -/
theorem toFinsupp_eq_of_eq [DecidableEq F] {a b : InteractionDelta F} (h : a = b) :
    a.toFinsupp = b.toFinsupp := by rw [h]

/-- Helper lemma: if collectAdds = 0, then toFinsupp of collectAdds = toFinsupp 0. -/
theorem toFinsupp_zero_of_eq_zero [DecidableEq F] {a : InteractionDelta F} (h : a = 0) :
    a.toFinsupp = (0 : InteractionDelta F).toFinsupp := by rw [h]

/-- Relates a foldl over List.finRange to a Finset.sum at the toFinsupp level.
    This is useful for proving localAdds_eq when localAdds is defined using foldl. -/
theorem toFinsupp_foldl_finRange [DecidableEq F] {n : ℕ} (f : Fin n → InteractionDelta F) :
    ((List.finRange n).foldl (fun acc i => acc + f i) 0).toFinsupp =
    ∑ i : Fin n, (f i).toFinsupp := by
  induction n with
  | zero =>
    simp only [List.finRange_zero, List.foldl_nil, Finset.univ_eq_empty, Finset.sum_empty]
    rfl
  | succ n ih =>
    -- Use the _last variant: finRange (n+1) = map castSucc (finRange n) ++ [last n]
    rw [List.finRange_succ_last, List.foldl_append, List.foldl_map, List.foldl_cons, List.foldl_nil]
    -- Show that foldl.toFinsupp = sum for the first n elements
    have ih' : ((List.finRange n).foldl (fun acc i => acc + f (Fin.castSucc i)) 0).toFinsupp =
        ∑ i : Fin n, (f (Fin.castSucc i)).toFinsupp := by
      have := ih (f ∘ Fin.castSucc)
      simp only [Function.comp_def] at this
      exact this
    rw [toFinsupp_add, ih', Fin.sum_univ_castSucc]

end InteractionDelta

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
  | add : (multiplicity : Expression F) → NamedList (Expression F) → FlatOperation F

inductive NestedOperations (F : Type) where
  | single : FlatOperation F → NestedOperations F
  | nested : String × List (NestedOperations F) → NestedOperations F

def NestedOperations.toFlat {F : Type} : NestedOperations F → List (FlatOperation F)
  | .single op => [op]
  | .nested (_, lst) => List.flatMap toFlat lst

namespace FlatOperation
instance [Repr F] : Repr (FlatOperation F) where
  reprPrec
  | witness m _, _ => "(Witness " ++ reprStr m ++ ")"
  | assert e, _ => "(Assert " ++ reprStr e ++ " == 0)"
  | lookup l, _ => reprStr l
  | add mult nl, _ => "(Add " ++ reprStr mult ++ " × " ++ reprStr nl ++ ")"

/--
What it means that "constraints hold" on a list of flat operations:
- For assertions, the expression must evaluate to 0
- For lookups, the evaluated entry must be in the table
- For add, there is no local constraint (balance checked globally)
-/
def ConstraintsHoldFlat (eval : Environment F) : List (FlatOperation F) → Prop
  | [] => True
  | op :: ops => match op with
    | assert e => (eval e = 0) ∧ ConstraintsHoldFlat eval ops
    | lookup l => l.Contains eval ∧ ConstraintsHoldFlat eval ops
    | _ => ConstraintsHoldFlat eval ops

@[circuit_norm]
def localLength : List (FlatOperation F) → ℕ
  | [] => 0
  | witness m _ :: ops => m + localLength ops
  | assert _ :: ops | lookup _ :: ops | add _ _ :: ops => localLength ops

@[circuit_norm]
def localWitnesses (env : Environment F) : (l : List (FlatOperation F)) → Vector F (localLength l)
  | [] => #v[]
  | witness _ compute :: ops => compute env ++ localWitnesses env ops
  | assert _ :: ops | lookup _ :: ops | add _ _ :: ops => localWitnesses env ops

/-- Induction principle for `FlatOperation`s. -/
def induct {motive : List (FlatOperation F) → Sort*}
  (empty : motive [])
  (witness : ∀ m c ops, motive ops → motive (.witness m c :: ops))
  (assert : ∀ e ops, motive ops → motive (.assert e :: ops))
  (lookup : ∀ l ops, motive ops → motive (.lookup l :: ops))
  (add : ∀ mult nl ops, motive ops → motive (.add mult nl :: ops))
    (ops : List (FlatOperation F)) : motive ops :=
  match ops with
  | [] => empty
  | .witness m c :: ops => witness m c ops (induct empty witness assert lookup add ops)
  | .assert e :: ops => assert e ops (induct empty witness assert lookup add ops)
  | .lookup l :: ops => lookup l ops (induct empty witness assert lookup add ops)
  | .add mult nl :: ops => add mult nl ops (induct empty witness assert lookup add ops)
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
  ops : NestedOperations F

  -- we have a low-level notion of "the constraints hold on these operations".
  -- for convenience, we allow the framework to transform that into custom `Soundness`,
  -- `Completeness` and `UsesLocalWitnesses` statements (which may involve inputs/outputs, assumptions on inputs, etc)
  Soundness : Environment F → Prop
  Completeness : Environment F → Prop
  UsesLocalWitnesses : Environment F → Prop

  -- for faster simplification, the subcircuit records its local witness length separately
  -- even though it could be derived from the operations
  localLength : ℕ

  -- compute the local interaction delta from this subcircuit's operations (defaults to empty)
  localAdds : Environment F → InteractionDelta F := fun _ => 0

  -- `Soundness` needs to follow from the constraints for any witness
  imply_soundness : ∀ env,
    ConstraintsHoldFlat env ops.toFlat → Soundness env

  -- `Completeness` needs to imply the constraints, when using the locally declared witness generators of this circuit
  implied_by_completeness : ∀ env, env.ExtendsVector (localWitnesses env ops.toFlat) offset →
    Completeness env → ConstraintsHoldFlat env ops.toFlat
  -- `UsesLocalWitnesses` needs to follow from the local witness generator condition
  imply_usesLocalWitnesses : ∀ env, env.ExtendsVector (localWitnesses env ops.toFlat) offset →
    UsesLocalWitnesses env

  -- `localLength` must be consistent with the operations
  localLength_eq : localLength = FlatOperation.localLength ops.toFlat

@[reducible, circuit_norm]
def Subcircuit.witnesses (sc : Subcircuit F n) env :=
  (FlatOperation.localWitnesses env sc.ops.toFlat).cast sc.localLength_eq.symm

/--
Core type representing the result of a circuit: a sequence of operations.

In addition to `witness`, `assert` and `lookup`,
`Operation` can also be a `subcircuit`, which itself is essentially a list of operations.
-/
inductive Operation (F : Type) [Field F] where
  | witness : (m : ℕ) → (compute : Environment F → Vector F m) → Operation F
  | assert : Expression F → Operation F
  | lookup : Lookup F → Operation F
  | subcircuit : {n : ℕ} → Subcircuit F n → Operation F
  | add : (multiplicity : Expression F) → NamedList (Expression F) → Operation F

namespace Operation
instance [Repr F] : Repr (Operation F) where
  reprPrec op _ := match op with
    | witness m _ => "(Witness " ++ reprStr m ++ ")"
    | assert e => "(Assert " ++ reprStr e ++ " == 0)"
    | lookup l => reprStr l
    | subcircuit { ops, .. } => "(Subcircuit " ++ reprStr ops.toFlat ++ ")"
    | add mult nl => "(Add " ++ reprStr mult ++ " × " ++ reprStr nl ++ ")"

/--
The number of witness variables introduced by this operation.
-/
@[circuit_norm]
def localLength : Operation F → ℕ
  | .witness m _ => m
  | .assert _ => 0
  | .lookup _ => 0
  | .subcircuit s => s.localLength
  | .add _ _ => 0

def localWitnesses (env : Environment F) : (op : Operation F) → Vector F op.localLength
  | .witness _ c => c env
  | .assert _ => #v[]
  | .lookup _ => #v[]
  | .subcircuit s => s.witnesses env
  | .add _ _ => #v[]
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
  | .add mult nl :: ops => .add mult nl :: toFlat ops
  | .subcircuit s :: ops => s.ops.toFlat ++ toFlat ops

def toNested : Operations F → List (NestedOperations F)
  | [] => []
  | .witness m c :: ops => .single (.witness m c) :: toNested ops
  | .assert e :: ops => .single (.assert e) :: toNested ops
  | .lookup l :: ops => .single (.lookup l) :: toNested ops
  | .add mult nl :: ops => .single (.add mult nl) :: toNested ops
  | .subcircuit s :: ops => s.ops :: toNested ops

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
  | .add _ _ :: ops => localLength ops

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
  | .add _ _ :: ops => localWitnesses env ops

/-- Induction principle for `Operations`. -/
def induct {motive : Operations F → Sort*}
  (empty : motive [])
  (witness : ∀ m c ops, motive ops → motive (.witness m c :: ops))
  (assert : ∀ e ops, motive ops → motive (.assert e :: ops))
  (lookup : ∀ l ops, motive ops → motive (.lookup l :: ops))
  (subcircuit : ∀ {n} (s : Subcircuit F n) ops, motive ops → motive (.subcircuit s :: ops))
  (add : ∀ mult nl ops, motive ops → motive (.add mult nl :: ops))
    (ops : Operations F) : motive ops :=
  match ops with
  | [] => empty
  | .witness m c :: ops => witness m c ops (induct empty witness assert lookup subcircuit add ops)
  | .assert e :: ops => assert e ops (induct empty witness assert lookup subcircuit add ops)
  | .lookup l :: ops => lookup l ops (induct empty witness assert lookup subcircuit add ops)
  | .subcircuit s :: ops => subcircuit s ops (induct empty witness assert lookup subcircuit add ops)
  | .add mult nl :: ops => add mult nl ops (induct empty witness assert lookup subcircuit add ops)

/-- Collect all add operations from the operations list, evaluating their expressions -/
def collectAdds (env : Environment F) : Operations F → InteractionDelta F
  | [] => 0
  | .add mult nl :: ops => InteractionDelta.single (nl.eval env) (mult.eval env) + collectAdds env ops
  | .witness _ _ :: ops => collectAdds env ops
  | .assert _ :: ops => collectAdds env ops
  | .lookup _ :: ops => collectAdds env ops
  | .subcircuit s :: ops => s.localAdds env + collectAdds env ops

@[circuit_norm]
theorem collectAdds_nil (env : Environment F) : collectAdds env ([] : Operations F) = 0 := rfl

@[circuit_norm]
theorem collectAdds_assert (env : Environment F) (e : Expression F) (ops : Operations F) :
    collectAdds env (.assert e :: ops) = collectAdds env ops := rfl

@[circuit_norm]
theorem collectAdds_witness (env : Environment F) (m : ℕ) (c : Environment F → Vector F m) (ops : Operations F) :
    collectAdds env (.witness m c :: ops) = collectAdds env ops := rfl

@[circuit_norm]
theorem collectAdds_lookup (env : Environment F) (l : Lookup F) (ops : Operations F) :
    collectAdds env (.lookup l :: ops) = collectAdds env ops := rfl

@[circuit_norm]
theorem collectAdds_append (env : Environment F) (ops1 ops2 : Operations F) :
    collectAdds env (ops1 ++ ops2) = collectAdds env ops1 + collectAdds env ops2 := by
  induction ops1 with
  | nil => simp only [List.nil_append, collectAdds, InteractionDelta.zero_add']
  | cons op ops1 ih =>
    cases op <;> simp only [List.cons_append, collectAdds, ih, InteractionDelta.add_assoc']

-- Helper: a + foldl (+) 0 xs = foldl (+) a xs for InteractionDelta
private theorem foldl_add_start {xs : List (InteractionDelta F)} {a : InteractionDelta F} :
    a + xs.foldl (· + ·) 0 = xs.foldl (· + ·) a := by
  induction xs generalizing a with
  | nil => simp only [List.foldl_nil, InteractionDelta.add_zero']
  | cons y ys ih =>
    simp only [List.foldl_cons, InteractionDelta.zero_add']
    rw [←ih (a:=y), ←ih (a:=a+y)]
    rw [InteractionDelta.add_assoc']

theorem collectAdds_flatten (env : Environment F) (opss : List (Operations F)) :
    collectAdds env opss.flatten = (opss.map (collectAdds env)).foldl (· + ·) 0 := by
  induction opss with
  | nil => rfl
  | cons ops opss ih =>
    simp only [List.flatten_cons, collectAdds_append, List.map_cons, List.foldl_cons,
      InteractionDelta.zero_add', ih, foldl_add_start]

-- Helper to convert between foldl forms
private theorem foldl_ofFn_eq {m : ℕ} {β : Type*} (f : Fin m → β) (g : β → β → β) (init : β) :
    (List.ofFn f).foldl g init = (List.finRange m).foldl (fun acc i => g acc (f i)) init := by
  induction m generalizing init with
  | zero => rfl
  | succ n ih =>
    simp only [List.ofFn_succ, List.finRange_succ, List.foldl_cons, List.foldl_map]
    exact ih (fun i => f i.succ) (g init (f 0))

theorem collectAdds_ofFn_flatten {m : ℕ} (env : Environment F) (f : Fin m → Operations F) :
    collectAdds env (List.ofFn f).flatten =
    (List.finRange m).foldl (fun acc i => acc + collectAdds env (f i)) 0 := by
  rw [collectAdds_flatten, List.map_ofFn, foldl_ofFn_eq]
  simp only [Function.comp_apply]

-- Version where f takes Nat and uses Fin.val coercion implicitly
theorem collectAdds_ofFn_flatten' {m : ℕ} (env : Environment F) (f : ℕ → Operations F) :
    collectAdds env (List.ofFn (fun i : Fin m => f ↑i)).flatten =
    (List.finRange m).foldl (fun acc i => acc + collectAdds env (f i.val)) 0 :=
  collectAdds_ofFn_flatten env (fun i => f ↑i)

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
  add (offset : ℕ) (_ : Expression F) (_ : NamedList (Expression F)) : Prop := True

@[circuit_norm]
def Condition.apply (condition : Condition F) (offset : ℕ) : Operation F → Prop
  | .witness m c => condition.witness offset m c
  | .assert e => condition.assert offset e
  | .lookup l => condition.lookup offset l
  | .subcircuit s => condition.subcircuit offset s
  | .add mult nl => condition.add offset mult nl

def Condition.implies (c c': Condition F) : Condition F where
  witness n m compute := c.witness n m compute → c'.witness n m compute
  assert offset e := c.assert offset e → c'.assert offset e
  lookup offset l := c.lookup offset l → c'.lookup offset l
  subcircuit offset _ s := c.subcircuit offset s → c'.subcircuit offset s
  add offset mult nl := c.add offset mult nl → c'.add offset mult nl

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
  | .add mult nl :: ops => condition.add offset mult nl ∧ forAll offset condition ops

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
  (add : ∀ n mult nl ops {h}, motive ops n h →
    motive (.add mult nl :: ops) n (by simp_all [SubcircuitsConsistent, forAll]))
    (ops : Operations F) (n : ℕ) (h : ops.SubcircuitsConsistent n) : motive ops n h :=
  motive' ops n h
where motive' : (ops : Operations F) → (n : ℕ) → (h : ops.SubcircuitsConsistent n) → motive ops n h
  | [], n, _ => empty n
  | .witness m c :: ops, n, h | .assert e :: ops, n, h | .lookup e :: ops, n, h | .add mult nl :: ops, n, h => by
    rw [SubcircuitsConsistent, forAll] at h
    first
    | exact witness _ _ _ _ (motive' ops _ h.right)
    | exact assert _ _ _ (motive' ops _ h.right)
    | exact lookup _ _ _ (motive' ops _ h.right)
    | exact add _ _ _ _ (motive' ops _ h.right)
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
  | .add mult nl => condition.add offset mult nl

def FlatOperation.singleLocalLength : FlatOperation F → ℕ
  | .witness m _ => m
  | .assert _ => 0
  | .lookup _ => 0
  | .add _ _ => 0

def FlatOperation.forAll (offset : ℕ) (condition : Condition F) : List (FlatOperation F) → Prop
  | [] => True
  | .witness m c :: ops => condition.witness offset m c ∧ forAll (m + offset) condition ops
  | .assert e :: ops => condition.assert offset e ∧ forAll offset condition ops
  | .lookup l :: ops => condition.lookup offset l ∧ forAll offset condition ops
  | .add mult nl :: ops => condition.add offset mult nl ∧ forAll offset condition ops

def Operations.forAllFlat (n : ℕ) (condition : Condition F) (ops : Operations F) : Prop :=
  forAll n { condition with subcircuit n _ s := FlatOperation.forAll n condition s.ops.toFlat } ops
