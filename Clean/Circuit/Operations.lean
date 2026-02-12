import Clean.Circuit.Expression
import Clean.Circuit.Lookup
import Clean.Circuit.Provable
import Clean.Circuit.Channel
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
  | interact : AbstractInteraction F → FlatOperation F

inductive NestedOperations (F : Type) where
  | single : FlatOperation F → NestedOperations F
  | nested : String × List (NestedOperations F) → NestedOperations F

def NestedOperations.toFlat {F : Type} : NestedOperations F → List (FlatOperation F)
  | .single op => [op]
  | .nested (_, lst) => List.flatMap toFlat lst

abbrev WitnessOperation (F : Type) := (m : ℕ) ×' (Environment F → Vector F m)

namespace FlatOperation
instance [Repr F] : Repr (FlatOperation F) where
  reprPrec
  | witness m _, _ => "(Witness " ++ reprStr m ++ ")"
  | assert e, _ => "(Assert " ++ reprStr e ++ " == 0)"
  | lookup l, _ => reprStr l
  | interact i, _ => "(Interact " ++ reprStr i ++ ")"

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
    | interact _ => ConstraintsHoldFlat eval ops
    | _ => ConstraintsHoldFlat eval ops

@[circuit_norm]
def localLength : List (FlatOperation F) → ℕ
  | [] => 0
  | witness m _ :: ops => m + localLength ops
  | assert _ :: ops | lookup _ :: ops | interact _ :: ops => localLength ops

@[circuit_norm]
def localWitnesses (env : Environment F) : (l : List (FlatOperation F)) → Vector F (localLength l)
  | [] => #v[]
  | witness _ compute :: ops => compute env ++ localWitnesses env ops
  | assert _ :: ops | lookup _ :: ops | interact _ :: ops => localWitnesses env ops

-- extracting individual types of operations

def constraints : List (FlatOperation F) → List (Expression F)
  | [] => []
  | assert e :: ops => e :: constraints ops
  | witness _ _ :: ops | lookup _ :: ops | interact _ :: ops => constraints ops

def lookups : List (FlatOperation F) → List (Lookup F)
  | [] => []
  | lookup l :: ops => l :: lookups ops
  | witness _ _ :: ops | assert _ :: ops | interact _ :: ops => lookups ops

def interactions : List (FlatOperation F) → List (AbstractInteraction F)
  | [] => []
  | interact i :: ops => i :: interactions ops
  | witness _ _ :: ops | assert _ :: ops | lookup _ :: ops => interactions ops

def witnessOperations : List (FlatOperation F) → List (WitnessOperation F)
  | [] => []
  | witness m c :: ops => ⟨m, c⟩ :: witnessOperations ops
  | assert _ :: ops | lookup _ :: ops | interact _ :: ops => witnessOperations ops

/-- Induction principle for `FlatOperation`s. -/
def induct {motive : List (FlatOperation F) → Sort*}
  (empty : motive [])
  (witness : ∀ m c ops, motive ops → motive (.witness m c :: ops))
  (assert : ∀ e ops, motive ops → motive (.assert e :: ops))
  (lookup : ∀ l ops, motive ops → motive (.lookup l :: ops))
  (interact : ∀ i ops, motive ops → motive (.interact i :: ops))
    (ops : List (FlatOperation F)) : motive ops :=
  match ops with
  | [] => empty
  | .witness m c :: ops => witness m c ops (induct empty witness assert lookup interact ops)
  | .assert e :: ops => assert e ops (induct empty witness assert lookup interact ops)
  | .lookup l :: ops => lookup l ops (induct empty witness assert lookup interact ops)
  | .interact i :: ops => interact i ops (induct empty witness assert lookup interact ops)

omit [Field F] in
lemma interactions_append {ops1 ops2 : List (FlatOperation F)} :
    interactions (ops1 ++ ops2) = interactions ops1 ++ interactions ops2 := by
  induction ops1 using FlatOperation.induct <;> simp_all [interactions]

/--
A `Condition` lets you define a predicate on operations, given the type and content of the
current operation as well as the current offset.
-/
structure Condition (F : Type) [Field F] where
  witness : (m : ℕ) → (Environment F → Vector F m) → Prop := fun _ _ => True
  assert (_ : Expression F) : Prop := True
  lookup (_ : Lookup F) : Prop := True
  interact (_ : AbstractInteraction F) : Prop := True

/--
Given a `Condition`, `forAll` is true iff all operations in the list satisfy the condition, at their respective offsets.
The function expects the initial offset as an argument.
-/
 @[circuit_norm]
def forAllNoOffset (condition : Condition F) (ops : List (FlatOperation F)) : Prop :=
  ops.Forall fun
  | .witness m c => condition.witness m c
  | .assert e => condition.assert e
  | .lookup l => condition.lookup l
  | .interact i => condition.interact i

/--
In proofs, the most convenient way of dealing with a forAll condition is to characterize them
as operating individually on different operation types.
-/
lemma forAllNoOffset_iff_forall_mem {condition : Condition F} {ops : List (FlatOperation F)} :
  forAllNoOffset condition ops ↔
    (∀ e ∈ constraints ops, condition.assert e) ∧
    (∀ l ∈ lookups ops, condition.lookup l) ∧
    (∀ i ∈ interactions ops, condition.interact i) ∧
    (∀ t ∈ witnessOperations ops, condition.witness t.1 t.2) := by
  simp only [forAllNoOffset, List.forall_iff_forall_mem]
  induction ops using FlatOperation.induct <;> (
    simp_all [constraints, lookups, interactions, witnessOperations]
    try tauto)

def ConstraintsHoldWithInteractions (eval : Environment F) :=
  forAllNoOffset {
    assert e := eval e = 0
    lookup l := l.Contains eval
    interact i := i.assumeGuarantees → i.Guarantees eval
  }

@[circuit_norm]
lemma constraintsHoldWithInteractions_iff_forall_mem {eval : Environment F}
    {ops : List (FlatOperation F)} :
  ConstraintsHoldWithInteractions eval ops ↔
    (∀ e ∈ constraints ops, eval e = 0) ∧
    (∀ l ∈ lookups ops, l.Contains eval) ∧
    (∀ i ∈ interactions ops, i.assumeGuarantees → i.Guarantees eval) := by
  simp [ConstraintsHoldWithInteractions, forAllNoOffset_iff_forall_mem]

def Guarantees (env : Environment F) : List (FlatOperation F) → Prop :=
  forAllNoOffset { interact i := i.assumeGuarantees → i.Guarantees env }

 @[circuit_norm]
lemma guarantees_iff_forall_mem {env : Environment F} {ops : List (FlatOperation F)} :
  Guarantees env ops ↔ (∀ i ∈ interactions ops, i.assumeGuarantees → i.Guarantees env) := by
  simp [Guarantees, forAllNoOffset_iff_forall_mem]

def Requirements (env : Environment F) : List (FlatOperation F) → Prop :=
  forAllNoOffset { interact i := i.Requirements env }

 @[circuit_norm]
lemma requirements_iff_forall_mem {env : Environment F} {ops : List (FlatOperation F)} :
  Requirements env ops ↔ (∀ i ∈ interactions ops, i.Requirements env) := by
  simp [Requirements, forAllNoOffset_iff_forall_mem]

def ChannelGuarantees (channel : RawChannel F) (env : Environment F) : List (FlatOperation F) → Prop :=
  forAllNoOffset { interact i := i.channel = channel → i.assumeGuarantees → i.Guarantees env }

 @[circuit_norm]
lemma channelGuarantees_iff_forall_mem {channel : RawChannel F} {env : Environment F}
    {ops : List (FlatOperation F)} :
  ChannelGuarantees channel env ops ↔
    (∀ i ∈ interactions ops, i.channel = channel → i.assumeGuarantees → i.Guarantees env) := by
  simp [ChannelGuarantees, forAllNoOffset_iff_forall_mem]

def ChannelRequirements (channel : RawChannel F) (env : Environment F) : List (FlatOperation F) → Prop :=
  forAllNoOffset { interact i := i.channel = channel → i.Requirements env }

@[circuit_norm]
lemma channelRequirements_iff_forall_mem {channel : RawChannel F} {env : Environment F}
    {ops : List (FlatOperation F)} :
  ChannelRequirements channel env ops ↔
    (∀ i ∈ interactions ops, i.channel = channel → i.Requirements env) := by
  simp [ChannelRequirements, forAllNoOffset_iff_forall_mem]

def InChannelsOrGuarantees (channels : List (RawChannel F)) (env : Environment F) :
    List (FlatOperation F) → Prop :=
  forAllNoOffset { interact i := i.channel ∈ channels ∨ (i.assumeGuarantees → i.Guarantees env) }

@[circuit_norm]
lemma inChannelsOrGuarantees_iff_forall_mem {channels : List (RawChannel F)} {env : Environment F}
    {ops : List (FlatOperation F)} :
  InChannelsOrGuarantees channels env ops ↔
    (∀ i ∈ interactions ops, i.channel ∈ channels ∨ (i.assumeGuarantees → i.Guarantees env)) := by
  simp [InChannelsOrGuarantees, forAllNoOffset_iff_forall_mem]

def InChannelsOrRequirements (channels : List (RawChannel F)) (env : Environment F) :
    List (FlatOperation F) → Prop :=
  forAllNoOffset { interact i := i.channel ∈ channels ∨ i.Requirements env }

@[circuit_norm]
lemma inChannelsOrRequirements_iff_forall_mem {channels : List (RawChannel F)} {env : Environment F}
    {ops : List (FlatOperation F)} :
  InChannelsOrRequirements channels env ops ↔
    (∀ i ∈ interactions ops, i.channel ∈ channels ∨ i.Requirements env) := by
  simp [InChannelsOrRequirements, forAllNoOffset_iff_forall_mem]

@[circuit_norm]
def localAdds (env : Environment F) : List (FlatOperation F) → InteractionDelta F
  | [] => 0
  | .witness _ _ :: ops => localAdds env ops
  | .assert _ :: ops => localAdds env ops
  | .lookup _ :: ops => localAdds env ops
  | .interact i :: ops => i.eval env :: localAdds env ops
end FlatOperation

export FlatOperation (ConstraintsHoldFlat)

-- TODO witness input here, and localWitnesses, should be arrays not vectors
@[circuit_norm]
def Environment.ExtendsVector (env : Environment F) (wit : Vector F n) (offset : ℕ) : Prop :=
  ∀ i : Fin n, env.get (offset + i.val) = wit[i.val]

open FlatOperation in
/--
This is a low-level way to model a subcircuit:
A nested list of circuit operations, instantiated at a certain offset.

To enable composition of formal proofs, subcircuits come with custom `Soundness` and `Completeness`
statements, which have to be compatible with the subcircuit's actual constraints.
-/
structure Subcircuit (F : Type) [Field F] (offset : ℕ) where
  ops : NestedOperations F

  -- we have a low-level notion of "the constraints hold on these operations".
  -- for convenience, we allow the framework to transform that into custom `Soundness`,
  -- `Completeness` and `UsesLocalWitnesses` statements (which may involve inputs/outputs, assumptions on inputs, etc)
  -- TODO we should separate Spec, Assumptions and ProverAssumptions here
  Soundness : Environment F → Prop
  Completeness : Environment F → Prop
  UsesLocalWitnesses : Environment F → Prop

  -- for faster simplification, the subcircuit records its local witness length separately
  -- even though it could be derived from the operations
  localLength : ℕ

  localAdds : Environment F → InteractionDelta F := fun _ => 0

  -- `Soundness` and local requirements need to follow from constraints and guarantees.
  imply_soundness : ∀ env,
    ConstraintsHoldFlat env ops.toFlat →
    FlatOperation.Guarantees env ops.toFlat →
    Soundness env ∧ FlatOperation.Requirements env ops.toFlat

  -- `Completeness` needs to imply constraints and guarantees, when using the locally declared witness generators
  implied_by_completeness : ∀ env, env.ExtendsVector (localWitnesses env ops.toFlat) offset →
    Completeness env → ConstraintsHoldFlat env ops.toFlat ∧ FlatOperation.Guarantees env ops.toFlat
  -- `UsesLocalWitnesses` needs to follow from the local witness generator condition
  imply_usesLocalWitnesses : ∀ env, env.ExtendsVector (localWitnesses env ops.toFlat) offset →
    UsesLocalWitnesses env

  -- `localLength` must be consistent with the operations
  localLength_eq : localLength = FlatOperation.localLength ops.toFlat

  -- `localAdds` must be consistent with the operations
  localAdds_eq : ∀ env, localAdds env = FlatOperation.localAdds env ops.toFlat

    -- expose the channel guarantees and requirements, for end-to-end proofs
  channelsWithGuarantees : List (RawChannel F) := []
  channelsWithRequirements : List (RawChannel F) := []

  -- TODO maybe we don't need that, if we have a lawfulness property separately
  guarantees_iff : ∀ env,
    InChannelsOrGuarantees channelsWithGuarantees env ops.toFlat
  requirements_iff : ∀ env,
    InChannelsOrRequirements channelsWithRequirements env ops.toFlat

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
  | interact : AbstractInteraction F → Operation F
  | subcircuit : {n : ℕ} → Subcircuit F n → Operation F

namespace Operation
instance [Repr F] : Repr (Operation F) where
  reprPrec op _ := match op with
    | witness m _ => "(Witness " ++ reprStr m ++ ")"
    | assert e => "(Assert " ++ reprStr e ++ " == 0)"
    | lookup l => reprStr l
    | interact i => reprStr i
    | subcircuit { ops, .. } => "(Subcircuit " ++ reprStr ops.toFlat ++ ")"

/--
The number of witness variables introduced by this operation.
-/
@[circuit_norm]
def localLength : Operation F → ℕ
  | .witness m _ => m
  | .assert _ => 0
  | .lookup _ => 0
  | .interact _ => 0
  | .subcircuit s => s.localLength

def localWitnesses (env : Environment F) : (op : Operation F) → Vector F op.localLength
  | .witness _ c => c env
  | .assert _ => #v[]
  | .lookup _ => #v[]
  | .interact _ => #v[]
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
  | .interact i :: ops => .interact i :: toFlat ops
  | .subcircuit s :: ops => s.ops.toFlat ++ toFlat ops

def toNested : Operations F → List (NestedOperations F)
  | [] => []
  | .witness m c :: ops => .single (.witness m c) :: toNested ops
  | .assert e :: ops => .single (.assert e) :: toNested ops
  | .lookup l :: ops => .single (.lookup l) :: toNested ops
  | .interact i :: ops => .single (.interact i) :: toNested ops
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
  | .interact _ :: ops => localLength ops
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
  | .interact _ :: ops => localWitnesses env ops
  | .subcircuit s :: ops => s.witnesses env ++ localWitnesses env ops

-- extracting individual types of operations

def constraints : Operations F → List (Expression F)
  | [] => []
  | .assert e :: ops => e :: constraints ops
  | .subcircuit s :: ops => FlatOperation.constraints s.ops.toFlat ++ constraints ops
  | .witness _ _ :: ops | .lookup _ :: ops | .interact _ :: ops => constraints ops

def lookups : Operations F → List (Lookup F)
  | [] => []
  | .lookup l :: ops => l :: lookups ops
  | .subcircuit s :: ops => FlatOperation.lookups s.ops.toFlat ++ lookups ops
  | .witness _ _ :: ops | .assert _ :: ops | .interact _ :: ops => lookups ops

def interactions : Operations F → List (AbstractInteraction F)
  | [] => []
  | .interact i :: ops => i :: interactions ops
  | .subcircuit s :: ops => FlatOperation.interactions s.ops.toFlat ++ interactions ops
  | .witness _ _ :: ops | .assert _ :: ops | .lookup _ :: ops => interactions ops

def shallowInteractions : Operations F → List (AbstractInteraction F)
  | [] => []
  | .interact i :: ops => i :: shallowInteractions ops
  | .witness _ _ :: ops | .assert _ :: ops | .lookup _ :: ops | .subcircuit _ :: ops
    => shallowInteractions ops

def witnessOperations : Operations F → List (WitnessOperation F)
  | [] => []
  | .witness m c :: ops => ⟨m, c⟩ :: witnessOperations ops
  | .subcircuit s :: ops => FlatOperation.witnessOperations s.ops.toFlat ++ witnessOperations ops
  | .assert _ :: ops | .lookup _ :: ops | .interact _ :: ops => witnessOperations ops

def subcircuits : Operations F → List ((n : ℕ) ×' Subcircuit F n)
  | [] => []
  | .subcircuit s :: ops => ⟨_, s⟩ :: subcircuits ops
  | .witness _ _ :: ops | .assert _ :: ops | .lookup _ :: ops | .interact _ :: ops => subcircuits ops

/-- Induction principle for `Operations`. -/
def induct {motive : Operations F → Sort*}
  (empty : motive [])
  (witness : ∀ m c ops, motive ops → motive (.witness m c :: ops))
  (assert : ∀ e ops, motive ops → motive (.assert e :: ops))
  (lookup : ∀ l ops, motive ops → motive (.lookup l :: ops))
  (interact : ∀ i ops, motive ops → motive (.interact i :: ops))
  (subcircuit : ∀ {n} (s : Subcircuit F n) ops, motive ops → motive (.subcircuit s :: ops))
    (ops : Operations F) : motive ops :=
  match ops with
  | [] => empty
  | .witness m c :: ops => witness m c ops (induct empty witness assert lookup interact subcircuit ops)
  | .assert e :: ops => assert e ops (induct empty witness assert lookup interact subcircuit ops)
  | .lookup l :: ops => lookup l ops (induct empty witness assert lookup interact subcircuit ops)
  | .subcircuit s :: ops => subcircuit s ops (induct empty witness assert lookup interact subcircuit ops)
  | .interact i :: ops => interact i ops (induct empty witness assert lookup interact subcircuit ops)

/-- Collect all add operations from the operations list, evaluating their expressions -/
def localAdds (env : Environment F) : Operations F → InteractionDelta F
  | [] => 0
  | .witness _ _ :: ops => localAdds env ops
  | .assert _ :: ops => localAdds env ops
  | .lookup _ :: ops => localAdds env ops
  | .interact i :: ops => .single (i.eval env) + localAdds env ops
  | .subcircuit s :: ops => s.localAdds env + localAdds env ops

open Classical in
@[circuit_norm]
noncomputable def interactionsWith (channel : RawChannel F) (ops : Operations F) :
    List (AbstractInteraction F) :=
  ops.interactions.filter fun i => i.channel = channel

-- TODO move all this to a theorems/lemmas file

@[circuit_norm]
theorem localAdds_nil (env : Environment F) : localAdds env ([] : Operations F) = [] := rfl

@[circuit_norm]
theorem localAdds_assert (env : Environment F) (e : Expression F) (ops : Operations F) :
    localAdds env (.assert e :: ops) = localAdds env ops := rfl
@[circuit_norm]
theorem localAdds_witness (env : Environment F) (m : ℕ) (c : Environment F → Vector F m) (ops : Operations F) :
    localAdds env (.witness m c :: ops) = localAdds env ops := rfl
@[circuit_norm]
theorem localAdds_lookup (env : Environment F) (l : Lookup F) (ops : Operations F) :
    localAdds env (.lookup l :: ops) = localAdds env ops := rfl
@[circuit_norm]
theorem localAdds_interact (env : Environment F) (i : AbstractInteraction F) (ops : Operations F) :
    localAdds env (.interact i :: ops) = .single (i.eval env) + localAdds env ops := rfl
@[circuit_norm]
theorem localAdds_subcircuit (env : Environment F) {n : ℕ} (s : Subcircuit F n) (ops : Operations F) :
    localAdds env (.subcircuit s :: ops) = s.localAdds env + localAdds env ops := rfl

@[circuit_norm]
theorem localAdds_append (env : Environment F) (ops1 ops2 : Operations F) :
    localAdds env (ops1 ++ ops2) = localAdds env ops1 + localAdds env ops2 := by
  induction ops1 with
  | nil => simp only [List.nil_append, localAdds, List.nil_append]; rfl
  | cons op ops1 ih =>
    cases op <;> simp only [List.cons_append, localAdds, ih, add_assoc]

@[circuit_norm]
theorem interactions_append (ops1 ops2 : Operations F) :
    interactions (ops1 ++ ops2) = interactions ops1 ++ interactions ops2 := by
  induction ops1 with
  | nil => rfl
  | cons op ops1 ih =>
    cases op <;> simp_all only [List.cons_append, interactions, List.append_assoc]

@[circuit_norm]
theorem interactionsWith_append (channel: RawChannel F) (ops1 ops2 : Operations F) :
    interactionsWith channel (ops1 ++ ops2) = interactionsWith channel ops1 ++ interactionsWith channel ops2 := by
  simp only [interactionsWith, interactions_append, List.filter_append]

-- Helper: a + foldl (+) 0 xs = foldl (+) a xs for InteractionDelta
omit [Field F] in
private theorem foldl_add_start {xs : List (RawInteractions F)} {a : RawInteractions F} :
    a + xs.foldl (· + ·) 0 = xs.foldl (· + ·) a := by
  induction xs generalizing a with
  | nil => simp only [List.foldl_nil, add_zero]
  | cons y ys ih =>
    simp only [List.foldl_cons, zero_add]
    rw [←ih (a:=y), ←ih (a:=a+y), add_assoc]

theorem localAdds_flatten (env : Environment F) (opss : List (Operations F)) :
    localAdds env opss.flatten = (opss.map (localAdds env)).foldl (· + ·) 0 := by
  induction opss with
  | nil => rfl
  | cons ops opss ih =>
    simp [List.flatten_cons, localAdds_append, List.map_cons, List.foldl_cons,
      ih, foldl_add_start]

-- Helper to convert between foldl forms
private theorem foldl_ofFn_eq {m : ℕ} {β : Type*} (f : Fin m → β) (g : β → β → β) (init : β) :
    (List.ofFn f).foldl g init = (List.finRange m).foldl (fun acc i => g acc (f i)) init := by
  induction m generalizing init with
  | zero => rfl
  | succ n ih =>
    simp only [List.ofFn_succ, List.finRange_succ, List.foldl_cons, List.foldl_map]
    exact ih (fun i => f i.succ) (g init (f 0))

theorem localAdds_ofFn_flatten {m : ℕ} (env : Environment F) (f : Fin m → Operations F) :
    localAdds env (List.ofFn f).flatten =
    (List.finRange m).foldl (fun acc i => acc + localAdds env (f i)) 0 := by
  rw [localAdds_flatten, List.map_ofFn, foldl_ofFn_eq]
  simp only [Function.comp_apply]

-- Version where f takes Nat and uses Fin.val coercion implicitly
theorem localAdds_ofFn_flatten' {m : ℕ} (env : Environment F) (f : ℕ → Operations F) :
    localAdds env (List.ofFn (fun i : Fin m => f ↑i)).flatten =
    (List.finRange m).foldl (fun acc i => acc ++ localAdds env (f i.val)) [] :=
  localAdds_ofFn_flatten env (fun i => f ↑i)

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
  interact (offset : ℕ) (_ : AbstractInteraction F) : Prop := True
  subcircuit (offset : ℕ) {m : ℕ} (_ : Subcircuit F m) : Prop := True

@[circuit_norm]
def Condition.apply (condition : Condition F) (offset : ℕ) : Operation F → Prop
  | .witness m c => condition.witness offset m c
  | .assert e => condition.assert offset e
  | .lookup l => condition.lookup offset l
  | .interact i => condition.interact offset i
  | .subcircuit s => condition.subcircuit offset s

def Condition.implies (c c': Condition F) : Condition F where
  witness n m compute := c.witness n m compute → c'.witness n m compute
  assert offset e := c.assert offset e → c'.assert offset e
  lookup offset l := c.lookup offset l → c'.lookup offset l
  interact offset i := c.interact offset i → c'.interact offset i
  subcircuit offset _ s := c.subcircuit offset s → c'.subcircuit offset s

structure ConditionWithInteractions (F : Type) [Field F] where
  witness (offset : ℕ) (is : RawInteractions F) (m : ℕ) (_ : Environment F → Vector F m) : Prop := True
  assert (offset : ℕ) (is : RawInteractions F) (_ : Expression F) : Prop := True
  lookup (offset : ℕ) (is : RawInteractions F) (_ : Lookup F) : Prop := True
  interact (offset : ℕ) (is : RawInteractions F) (_ : AbstractInteraction F) : Prop := True
  subcircuit (offset : ℕ) (is : RawInteractions F) {m : ℕ} (_ : Subcircuit F m) : Prop := True

structure ConditionNoOffset (F : Type) [Field F] where
  witness (m : ℕ) (_ : Environment F → Vector F m) : Prop := True
  assert (_ : Expression F) : Prop := True
  lookup (_ : Lookup F) : Prop := True
  interact (_ : AbstractInteraction F) : Prop := True
  subcircuit {m : ℕ} (_ : Subcircuit F m) : Prop := True

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
  | .interact i :: ops => condition.interact offset i ∧ forAll offset condition ops
  | .subcircuit s :: ops => condition.subcircuit offset s ∧ forAll (s.localLength + offset) condition ops

/--
Given a `ConditionNoOffset`, `forAllNoOffset` is true iff all operations in the list satisfy the condition.
-/
 @[circuit_norm]
def forAllNoOffset (condition : ConditionNoOffset F) : Operations F → Prop
  | [] => True
  | .witness m c :: ops => condition.witness m c ∧ forAllNoOffset condition ops
  | .assert e :: ops => condition.assert e ∧ forAllNoOffset condition ops
  | .lookup l :: ops => condition.lookup l ∧ forAllNoOffset condition ops
  | .interact i :: ops => condition.interact i ∧ forAllNoOffset condition ops
  | .subcircuit s :: ops => condition.subcircuit s ∧ forAllNoOffset condition ops

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
  (interact : ∀ n i ops {h}, motive ops n h →
    motive (.interact i :: ops) n (by simp_all [SubcircuitsConsistent, forAll]))
  (subcircuit : ∀ n (s : Subcircuit F n) ops {h}, motive ops (s.localLength + n) h →
    motive (.subcircuit s :: ops) n (by simp_all [SubcircuitsConsistent, forAll]))
    (ops : Operations F) (n : ℕ) (h : ops.SubcircuitsConsistent n) : motive ops n h :=
  motive' ops n h
where motive' : (ops : Operations F) → (n : ℕ) → (h : ops.SubcircuitsConsistent n) → motive ops n h
  | [], n, _ => empty n
  | .witness m c :: ops, n, h | .assert e :: ops, n, h
  | .lookup e :: ops, n, h | .interact i :: ops, n, h => by
    rw [SubcircuitsConsistent, forAll] at h
    first
    | exact witness _ _ _ _ (motive' ops _ h.right)
    | exact assert _ _ _ (motive' ops _ h.right)
    | exact lookup _ _ _ (motive' ops _ h.right)
    | exact interact _ _ _ (motive' ops _ h.right)
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
  | .interact i => condition.interact offset i

namespace FlatOperation
def singleLocalLength : FlatOperation F → ℕ
  | .witness m _ => m
  | .assert _ => 0
  | .lookup _ => 0
  | .interact _ => 0

def forAll (offset : ℕ) (condition : _root_.Condition F) : List (FlatOperation F) → Prop
  | [] => True
  | .witness m c :: ops => condition.witness offset m c ∧ forAll (m + offset) condition ops
  | .assert e :: ops => condition.assert offset e ∧ forAll offset condition ops
  | .lookup l :: ops => condition.lookup offset l ∧ forAll offset condition ops
  | .interact i :: ops => condition.interact offset i ∧ forAll offset condition ops
end FlatOperation

namespace Operations
def forAllFlat (n : ℕ) (condition : Condition F) (ops : Operations F) : Prop :=
  forAll n { condition with subcircuit n _ s := FlatOperation.forAll n condition s.ops.toFlat } ops

-- class Condition.Consistent (F : Type) [Field F] (condition : ConditionNoOffset F) : Prop where
--   consistent : ∀ s, condition.subcircuit s ↔ FlatOperation.forAllNoOffset condition s.ops.toFlat

-- not true in general, would need consistency condition
-- lemma forAllNoOffset_iff_forall_mem {condition : ConditionNoOffset F} {ops : Operations F} :
--   forAllNoOffset condition ops ↔
--     (∀ e ∈ constraints ops, condition.assert e) ∧
--     (∀ l ∈ lookups ops, condition.lookup l) ∧
--     (∀ i ∈ interactions ops, condition.interact i) ∧
--     (∀ t ∈ witnessOperations ops, condition.witness t.1 t.2) := by
--   sorry

@[circuit_norm]
def ConstraintsHold (env : Environment F) (ops : Operations F) : Prop :=
  (∀ e ∈ ops.constraints, env e = 0) ∧ (∀ l ∈ ops.lookups, l.Contains env)

def subcircuitChannelsWithGuarantees (ops : Operations F) : List (RawChannel F) :=
  ops.map (fun
    | .subcircuit s => s.channelsWithGuarantees
    | .witness _ _ | .assert _ | .lookup _ | .interact _ => [])
  |> List.flatten

-- simp lemmas
@[circuit_norm]
theorem subcircuitChannelsWithGuarantees_nil : subcircuitChannelsWithGuarantees ([] : Operations F) = [] := rfl
@[circuit_norm]
theorem subcircuitChannelsWithGuarantees_witness (m : ℕ) (c : Environment F → Vector F m) (ops : Operations F) :
    subcircuitChannelsWithGuarantees (.witness m c :: ops) = subcircuitChannelsWithGuarantees ops := rfl
@[circuit_norm]
theorem subcircuitChannelsWithGuarantees_assert (e : Expression F) (ops : Operations F) :
    subcircuitChannelsWithGuarantees (.assert e :: ops) = subcircuitChannelsWithGuarantees ops := rfl
@[circuit_norm]
theorem subcircuitChannelsWithGuarantees_lookup (l : Lookup F) (ops : Operations F) :
    subcircuitChannelsWithGuarantees (.lookup l :: ops) = subcircuitChannelsWithGuarantees ops := rfl
@[circuit_norm]
theorem subcircuitChannelsWithGuarantees_interact (i : AbstractInteraction F) (ops : Operations F) :
    subcircuitChannelsWithGuarantees (.interact i :: ops) = subcircuitChannelsWithGuarantees ops := rfl
@[circuit_norm]
theorem subcircuitChannelsWithGuarantees_subcircuit {n : ℕ} (s : Subcircuit F n) (ops : Operations F) :
    subcircuitChannelsWithGuarantees (.subcircuit s :: ops) =
    s.channelsWithGuarantees ++ subcircuitChannelsWithGuarantees ops := rfl

def subcircuitChannelsWithRequirements (ops : Operations F) : List (RawChannel F) :=
  ops.map (fun
    | .subcircuit s => s.channelsWithRequirements
    | .witness _ _ | .assert _ | .lookup _ | .interact _ => [])
  |> List.flatten

-- simp lemmas
@[circuit_norm]
theorem subcircuitChannelsWithRequirements_nil : subcircuitChannelsWithRequirements ([] : Operations F) = [] := rfl
@[circuit_norm]
theorem subcircuitChannelsWithRequirements_witness (m : ℕ) (c : Environment F → Vector F m) (ops : Operations F) :
    subcircuitChannelsWithRequirements (.witness m c :: ops) = subcircuitChannelsWithRequirements ops := rfl
@[circuit_norm]
theorem subcircuitChannelsWithRequirements_assert (e : Expression F) (ops : Operations F) :
    subcircuitChannelsWithRequirements (.assert e :: ops) = subcircuitChannelsWithRequirements ops := rfl
@[circuit_norm]
theorem subcircuitChannelsWithRequirements_lookup (l : Lookup F) (ops : Operations F) :
    subcircuitChannelsWithRequirements (.lookup l :: ops) = subcircuitChannelsWithRequirements ops := rfl
@[circuit_norm]
theorem subcircuitChannelsWithRequirements_interact (i : AbstractInteraction F) (ops : Operations F) :
    subcircuitChannelsWithRequirements (.interact i :: ops) = subcircuitChannelsWithRequirements ops := rfl
@[circuit_norm]
theorem subcircuitChannelsWithRequirements_subcircuit {n : ℕ} (s : Subcircuit F n) (ops : Operations F) :
    subcircuitChannelsWithRequirements (.subcircuit s :: ops) =
    s.channelsWithRequirements ++ subcircuitChannelsWithRequirements ops := rfl

-- TODO rename to ShallowGuarantees
@[circuit_norm]
def Guarantees (env : Environment F) (ops : Operations F) : Prop :=
  ops.forAllNoOffset { interact i := i.assumeGuarantees → i.Guarantees env }

lemma interactions_toFlat {ops : Operations F} :
    FlatOperation.interactions ops.toFlat = ops.interactions := by
  induction ops using Operations.induct with
  | empty | witness | assert | lookup | interact =>
    simp_all [interactions, FlatOperation.interactions, Operations.toFlat]
  | subcircuit s ops ih =>
    simp_all [interactions, FlatOperation.interactions_append, Operations.toFlat]

lemma guarantees_iff_forall_mem {env : Environment F} {ops : Operations F} :
    Guarantees env ops ↔
    ∀ i ∈ ops.shallowInteractions, i.assumeGuarantees → i.Guarantees env := by
  simp only [Guarantees]
  induction ops using Operations.induct <;>
    simp_all [circuit_norm, shallowInteractions]

@[circuit_norm]
def FullGuarantees (env : Environment F) (ops : Operations F) : Prop :=
  ∀ i ∈ ops.interactions, i.assumeGuarantees → i.Guarantees env

-- TODO rename to ShallowRequirements
@[circuit_norm]
def Requirements (env : Environment F) (ops : Operations F) : Prop :=
  ops.forAllNoOffset { interact i := i.Requirements env }

lemma requirements_iff_forall_mem {env : Environment F} {ops : Operations F} :
    Requirements env ops ↔
    ∀ i ∈ ops.shallowInteractions, i.Requirements env := by
  simp only [Requirements]
  induction ops using Operations.induct <;>
    simp_all [circuit_norm, shallowInteractions]

@[circuit_norm]
def FullRequirements (env : Environment F) (ops : Operations F) : Prop :=
  ∀ i ∈ ops.interactions, i.Requirements env

@[circuit_norm]
def ChannelGuarantees (channel : RawChannel F) (env : Environment F) (ops : Operations F) :=
  ∀ i ∈ ops.interactions, i.channel = channel → i.assumeGuarantees → i.Guarantees env

@[circuit_norm]
def ChannelRequirements (channel : RawChannel F) (env : Environment F) (ops : Operations F) :=
  ∀ i ∈ ops.interactions, i.channel = channel → i.Requirements env

@[circuit_norm]
def InChannelsOrGuarantees (channels : List (RawChannel F)) (env : Environment F)
    (ops : Operations F) : Prop :=
  ops.forAllNoOffset { interact i := i.channel ∈ channels ∨ (i.assumeGuarantees → i.Guarantees env) }

lemma inChannelsOrGuarantees_iff_forall_mem {channels : List (RawChannel F)} {env : Environment F} {ops : Operations F} :
    InChannelsOrGuarantees channels env ops ↔
    ∀ i ∈ ops.shallowInteractions, i.channel ∈ channels ∨ (i.assumeGuarantees → i.Guarantees env) := by
  simp only [InChannelsOrGuarantees]
  induction ops using Operations.induct <;> simp_all [circuit_norm, shallowInteractions]

@[circuit_norm]
def InChannelsOrGuaranteesFull (channels : List (RawChannel F)) (env : Environment F) (ops : Operations F) : Prop :=
  ∀ i ∈ ops.interactions, i.channel ∈ channels ∨ (i.assumeGuarantees → i.Guarantees env)

@[circuit_norm]
def InChannelsOrRequirements (channels : List (RawChannel F)) (env : Environment F)
    (ops : Operations F) : Prop :=
  ops.forAllNoOffset { interact i := i.channel ∈ channels ∨ i.Requirements env }

lemma inChannelsOrRequirements_iff_forall_mem {channels : List (RawChannel F)} {env : Environment F} {ops : Operations F} :
    InChannelsOrRequirements channels env ops ↔
    ∀ i ∈ ops.shallowInteractions, i.channel ∈ channels ∨ i.Requirements env := by
  simp only [InChannelsOrRequirements]
  induction ops using Operations.induct <;> simp_all [circuit_norm, shallowInteractions]

@[circuit_norm]
def InChannelsOrRequirementsFull (channels : List (RawChannel F)) (env : Environment F) (ops : Operations F) : Prop :=
  ∀ i ∈ ops.interactions, i.channel ∈ channels ∨ i.Requirements env
end Operations

@[circuit_norm]
def ConstraintsHoldWithInteractions.Soundness (env : Environment F)
    (ops : Operations F) : Prop :=
  ops.forAllNoOffset {
    assert e := env e = 0
    lookup l := l.Soundness env
    interact i := i.assumeGuarantees → i.Guarantees env
    subcircuit s := s.Soundness env
  }

-- open Operations in
-- lemma constraintsHoldWithInteractions_soundness_iff_forall_mem {env : Environment F} {ops : Operations F} :
--     ConstraintsHoldWithInteractions.Soundness env ops ↔
--     (∀ e ∈ ops.constraints, env e = 0) ∧
--     (∀ l ∈ ops.lookups, l.Soundness env) ∧
--     (∀ i ∈ ops.shallowInteractions, i.assumeGuarantees → i.Guarantees env) ∧
--     (∀ s ∈ ops.subcircuits, s.2.Soundness env) := by
--   simp only [ConstraintsHoldWithInteractions.Soundness]
--   induction ops using Operations.induct <;>
--     simp_all [circuit_norm, constraints, lookups, shallowInteractions, subcircuits]

@[circuit_norm]
def ConstraintsHoldWithInteractions.Completeness (env : Environment F)
    (ops : Operations F) : Prop :=
  ops.forAllNoOffset {
    assert e := env e = 0
    lookup l := l.Completeness env
    interact i := i.assumeGuarantees → i.Guarantees env
    subcircuit s := s.Completeness env
  }
