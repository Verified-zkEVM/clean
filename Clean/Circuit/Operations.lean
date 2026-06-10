import Clean.Circuit.Expression
import Clean.Circuit.WitnessIR
import Clean.Circuit.Lookup
import Clean.Circuit.Provable
import Clean.Circuit.Channel
import Clean.Circuit.SimpGadget

variable {F : Type} [FiniteField F] {α : Type} {n : ℕ}

/--
`FlatOperation` models the operations that can be done in a circuit, in a simple/flat way.

This is an intermediary type on the way to defining the full inductive `Operation` type.
It is needed because we already need to talk about operations in the `Subcircuit` definition,
which in turn is needed to define `Operation`.
-/
inductive FlatOperation (F : Type) where
  | witness : (m : ℕ) → WitgenIR F m → FlatOperation F
  | assert : Expression F → FlatOperation F
  | lookup : Lookup F → FlatOperation F
  | interact : AbstractInteraction F → FlatOperation F

inductive NestedOperations (F : Type) where
  | single : FlatOperation F → NestedOperations F
  | nested : String × List (NestedOperations F) → NestedOperations F

def NestedOperations.toFlat {F : Type} : NestedOperations F → List (FlatOperation F)
  | .single op => [op]
  | .nested (_, lst) => List.flatMap toFlat lst

abbrev WitnessOperation (F : Type) := (m : ℕ) ×' WitgenIR F m

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
- For interactions, there is no local constraint (balance checked globally)
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
  | assert _ :: ops | lookup _ :: ops | interact _ :: ops => localLength ops

@[circuit_norm]
def localWitnesses (env : ProverEnvironment F) : (l : List (FlatOperation F)) → Vector F (localLength l)
  | [] => #v[]
  | witness _ compute :: ops => compute.eval env ++ localWitnesses env ops
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

omit [FiniteField F] in @[circuit_norm]
lemma witnessOperations_append {ops1 ops2 : List (FlatOperation F)} :
    witnessOperations (ops1 ++ ops2) = witnessOperations ops1 ++ witnessOperations ops2 := by
  induction ops1 using FlatOperation.induct <;> simp_all [witnessOperations]

omit [FiniteField F] in @[circuit_norm]
lemma constraints_append {ops1 ops2 : List (FlatOperation F)} :
    constraints (ops1 ++ ops2) = constraints ops1 ++ constraints ops2 := by
  induction ops1 using FlatOperation.induct <;> simp_all [constraints]

omit [FiniteField F] in @[circuit_norm]
lemma lookups_append {ops1 ops2 : List (FlatOperation F)} :
    lookups (ops1 ++ ops2) = lookups ops1 ++ lookups ops2 := by
  induction ops1 using FlatOperation.induct <;> simp_all [lookups]

omit [FiniteField F] in @[circuit_norm]
lemma interactions_append {ops1 ops2 : List (FlatOperation F)} :
    interactions (ops1 ++ ops2) = interactions ops1 ++ interactions ops2 := by
  induction ops1 using FlatOperation.induct <;> simp_all [interactions]

lemma constraintsHoldFlat_iff_forall_mem {eval : Environment F} {ops : List (FlatOperation F)} :
  ConstraintsHoldFlat eval ops ↔
    (∀ e ∈ constraints ops, eval e = 0) ∧
    (∀ l ∈ lookups ops, l.Contains eval) := by
  induction ops using FlatOperation.induct <;>
    simp_all [ConstraintsHoldFlat, constraints, lookups, and_assoc]
  tauto

/--
A `Condition` lets you define a predicate on operations, given the type and content of the
current operation as well as the current offset.
-/
structure Condition (F : Type) [FiniteField F] where
  witness : (m : ℕ) → WitgenIR F m → Prop := fun _ _ => True
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

def ConstraintsHold (eval : Environment F) :=
  forAllNoOffset {
    assert e := eval e = 0
    lookup l := l.Contains eval
    interact i := i.Guarantees eval
  }

@[circuit_norm]
lemma constraintsHold_iff_forall_mem {eval : Environment F}
    {ops : List (FlatOperation F)} :
  ConstraintsHold eval ops ↔
    (∀ e ∈ constraints ops, eval e = 0) ∧
    (∀ l ∈ lookups ops, l.Contains eval) ∧
    (∀ i ∈ interactions ops, i.Guarantees eval) := by
  simp [ConstraintsHold, forAllNoOffset_iff_forall_mem]

def Guarantees (env : Environment F) : List (FlatOperation F) → Prop :=
  forAllNoOffset { interact i := i.Guarantees env }

 @[circuit_norm]
lemma guarantees_iff_forall_mem {env : Environment F} {ops : List (FlatOperation F)} :
  Guarantees env ops ↔ (∀ i ∈ interactions ops, i.Guarantees env) := by
  simp [Guarantees, forAllNoOffset_iff_forall_mem]

def Requirements (env : Environment F) : List (FlatOperation F) → Prop :=
  forAllNoOffset { interact i := i.Requirements env }

 @[circuit_norm]
lemma requirements_iff_forall_mem {env : Environment F} {ops : List (FlatOperation F)} :
  Requirements env ops ↔ (∀ i ∈ interactions ops, i.Requirements env) := by
  simp [Requirements, forAllNoOffset_iff_forall_mem]

def ChannelGuarantees (channel : RawChannel F) (env : Environment F) : List (FlatOperation F) → Prop :=
  forAllNoOffset { interact i := i.channel = channel → i.Guarantees env }

 @[circuit_norm]
lemma channelGuarantees_iff_forall_mem {channel : RawChannel F} {env : Environment F}
    {ops : List (FlatOperation F)} :
  ChannelGuarantees channel env ops ↔
    (∀ i ∈ interactions ops, i.channel = channel → i.Guarantees env) := by
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
  forAllNoOffset { interact i := i.channel ∈ channels ∨ i.Guarantees env }

@[circuit_norm]
lemma inChannelsOrGuarantees_iff_forall_mem {channels : List (RawChannel F)} {env : Environment F}
    {ops : List (FlatOperation F)} :
  InChannelsOrGuarantees channels env ops ↔
    (∀ i ∈ interactions ops, i.channel ∈ channels ∨ i.Guarantees env) := by
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

def channels (ops : List (FlatOperation F)) : List (RawChannel F) :=
  FlatOperation.interactions ops |>.map (·.channel)
end FlatOperation

export FlatOperation (ConstraintsHoldFlat)

-- TODO witness input here, and localWitnesses, should be arrays not vectors
@[circuit_norm]
def ProverEnvironment.ExtendsVector (env : ProverEnvironment F) (wit : Vector F n) (offset : ℕ) : Prop :=
  ∀ i : Fin n, env.get (offset + i.val) = wit[i.val]

open FlatOperation in
/--
This is a low-level way to model a subcircuit:
A nested list of circuit operations, instantiated at a certain offset.

To enable composition of formal proofs, subcircuits come with custom
`Spec`, `Assumptions`, `ProverSpec` and `ProverAssumptions`
statements, which have to be compatible with the subcircuit's actual constraints.
-/
structure Subcircuit (F : Type) [FiniteField F] (offset : ℕ) where
  ops : NestedOperations F

  -- we have a low-level notion of "the constraints hold on these operations".
  -- for convenience, we allow the framework to transform that into custom `Spec`, `Assumptions`,
  -- `ProverAssumptions` and `ProverSpec` statements (which may involve inputs/outputs, assumptions on inputs, etc)
  Assumptions : Environment F → Prop
  Spec : Environment F → Prop
  ProverAssumptions : ProverEnvironment F → Prop
  ProverSpec : ProverEnvironment F → Prop

  -- for faster simplification, the subcircuit records its local witness length separately
  -- even though it could be derived from the operations
  localLength : ℕ

  -- soundness: `Spec` and local requirements need to follow from assumptions, constraints and guarantees.
  soundness : ∀ env,
    Assumptions env →
    ConstraintsHoldFlat env ops.toFlat →
    FlatOperation.Guarantees env ops.toFlat →
    Spec env ∧ FlatOperation.Requirements env ops.toFlat

  -- completeness: `ProverAssumptions` needs to imply the constraints and guarantees,
  -- when using the locally declared witness generators of this circuit.
  -- `ProverSpec` also needs to follow from the local witness generator condition.
  completeness : ∀ env, env.ExtendsVector (localWitnesses env ops.toFlat) offset →
    (ProverAssumptions env →
      ConstraintsHoldFlat env ops.toFlat ∧ FlatOperation.Guarantees env ops.toFlat) ∧
    ProverSpec env

  -- `localLength` must be consistent with the operations
  localLength_eq : localLength = FlatOperation.localLength ops.toFlat

    -- expose the channel guarantees and requirements, for end-to-end proofs
  channelsWithGuarantees : List (RawChannel F) := []
  channelsWithRequirements : List (RawChannel F) := []

def Subcircuit.ChannelsLawful (s : Subcircuit F n) : Prop :=
  (∀ env, FlatOperation.InChannelsOrGuarantees s.channelsWithGuarantees env s.ops.toFlat) ∧
  (∀ env, FlatOperation.InChannelsOrRequirements s.channelsWithRequirements env s.ops.toFlat) ∧
  FlatOperation.channels s.ops.toFlat ⊆ s.channelsWithGuarantees ++ s.channelsWithRequirements

@[reducible, circuit_norm]
def Subcircuit.witnesses (sc : Subcircuit F n) env :=
  (FlatOperation.localWitnesses env sc.ops.toFlat).cast sc.localLength_eq.symm

/--
Core type representing the result of a circuit: a sequence of operations.

In addition to `witness`, `assert` and `lookup`,
`Operation` can also be a `subcircuit`, which itself is essentially a list of operations.
-/
inductive Operation (F : Type) [FiniteField F] where
  | witness : (m : ℕ) → (compute : WitgenIR F m) → Operation F
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

def localWitnesses (env : ProverEnvironment F) : (op : Operation F) → Vector F op.localLength
  | .witness _ c => c.eval env
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
def Operations (F : Type) [FiniteField F] := List (Operation F)

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
def localWitnesses (env : ProverEnvironment F) :
    (ops : Operations F) → Vector F ops.localLength
  | [] => #v[]
  | .witness _ c :: ops => c.eval env ++ localWitnesses env ops
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

def shallowConstraints : Operations F → List (Expression F)
  | [] => []
  | .assert e :: ops => e :: shallowConstraints ops
  | .witness _ _ :: ops | .lookup _ :: ops | .interact _ :: ops | .subcircuit _ :: ops
    => shallowConstraints ops

def lookups : Operations F → List (Lookup F)
  | [] => []
  | .lookup l :: ops => l :: lookups ops
  | .subcircuit s :: ops => FlatOperation.lookups s.ops.toFlat ++ lookups ops
  | .witness _ _ :: ops | .assert _ :: ops | .interact _ :: ops => lookups ops

def shallowLookups : Operations F → List (Lookup F)
  | [] => []
  | .lookup l :: ops => l :: shallowLookups ops
  | .witness _ _ :: ops | .assert _ :: ops | .interact _ :: ops | .subcircuit _ :: ops
    => shallowLookups ops

def interactions : Operations F → List (AbstractInteraction F)
  | [] => []
  | .interact i :: ops => i :: interactions ops
  | .subcircuit s :: ops => FlatOperation.interactions s.ops.toFlat ++ interactions ops
  | .witness _ _ :: ops | .assert _ :: ops | .lookup _ :: ops => interactions ops

open Classical in
/-- All interactions on a specific channel. -/
noncomputable def interactionsWith (channel : RawChannel F) (ops : Operations F) :
    List (AbstractInteraction F) :=
  ops.interactions.filter (fun i => i.channel = channel)

@[circuit_norm] lemma interactionsWith_nil (channel : RawChannel F) :
  interactionsWith channel ([] : Operations F) = [] := rfl

@[circuit_norm] lemma interactionsWith_witness (channel : RawChannel F)
    (m : ℕ) (c : WitgenIR F m) (ops : Operations F) :
  interactionsWith channel (.witness m c :: ops) = interactionsWith channel ops := rfl

@[circuit_norm] lemma interactionsWith_assert (channel : RawChannel F)
    (e : Expression F) (ops : Operations F) :
  interactionsWith channel (.assert e :: ops) = interactionsWith channel ops := rfl

@[circuit_norm] lemma interactionsWith_lookup (channel : RawChannel F)
    (l : Lookup F) (ops : Operations F) :
  interactionsWith channel (.lookup l :: ops) = interactionsWith channel ops := rfl

open Classical in
@[circuit_norm] lemma interactionsWith_interact (channel : RawChannel F)
    (i : AbstractInteraction F) (ops : Operations F) :
  interactionsWith channel (.interact i :: ops) =
    if i.channel = channel then i :: interactionsWith channel ops else interactionsWith channel ops := by
  by_cases h : i.channel = channel <;> simp [interactionsWith, interactions, h]

open Classical in
@[circuit_norm] lemma interactionsWith_subcircuit (channel : RawChannel F)
    {n : ℕ} (s : Subcircuit F n) (ops : Operations F) :
  interactionsWith channel (.subcircuit s :: ops) =
    (FlatOperation.interactions s.ops.toFlat).filter (fun i => i.channel = channel) ++
      interactionsWith channel ops := by
  simp [interactionsWith, interactions]

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

def shallowWitnessOperations : Operations F → List (WitnessOperation F)
  | [] => []
  | .witness m c :: ops => ⟨m, c⟩ :: shallowWitnessOperations ops
  | .assert _ :: ops | .lookup _ :: ops | .interact _ :: ops | .subcircuit _ :: ops
    => shallowWitnessOperations ops

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

-- link lemmas between flat and nested operations

lemma forall_constraints_iff {ops : Operations F} {motive : Expression F → Prop} :
  (∀ e ∈ constraints ops, motive e) ↔
    (∀ e ∈ shallowConstraints ops, motive e) ∧
    (∀ s ∈ subcircuits ops, ∀ e ∈ FlatOperation.constraints s.2.ops.toFlat, motive e) := by
  induction ops using induct; all_goals
  simp only [constraints, shallowConstraints, subcircuits, List.mem_append, List.mem_cons, or_imp, forall_and, forall_eq]
  try tauto

lemma forall_lookups_iff {ops : Operations F} {motive : Lookup F → Prop} :
  (∀ l ∈ lookups ops, motive l) ↔
    (∀ l ∈ shallowLookups ops, motive l) ∧
    (∀ s ∈ subcircuits ops, ∀ l ∈ FlatOperation.lookups s.2.ops.toFlat, motive l) := by
  induction ops using induct; all_goals
  simp only [lookups, shallowLookups, subcircuits, List.mem_append, List.mem_cons, or_imp, forall_and, forall_eq]
  try tauto

lemma forall_interactions_iff {ops : Operations F} {motive : AbstractInteraction F → Prop} :
  (∀ i ∈ interactions ops, motive i) ↔
    (∀ i ∈ shallowInteractions ops, motive i) ∧
    (∀ s ∈ subcircuits ops, ∀ i ∈ FlatOperation.interactions s.2.ops.toFlat, motive i) := by
  induction ops using induct; all_goals
  simp only [interactions, shallowInteractions, subcircuits, List.mem_append, List.mem_cons, or_imp, forall_and, forall_eq]
  try tauto

lemma forall_witnessOperations_iff {ops : Operations F} {motive : WitnessOperation F → Prop} :
  (∀ t ∈ witnessOperations ops, motive t) ↔
    (∀ t ∈ shallowWitnessOperations ops, motive t) ∧
    (∀ s ∈ subcircuits ops, ∀ t ∈ FlatOperation.witnessOperations s.2.ops.toFlat, motive t) := by
  induction ops using induct; all_goals
  simp only [witnessOperations, shallowWitnessOperations, subcircuits, List.mem_append, List.mem_cons, or_imp, forall_and, forall_eq]
  try tauto
end Operations

-- generic folding over `Operations` resulting in a proposition

/--
A `Condition` lets you define a predicate on operations, given the type and content of the
current operation as well as the current offset.
-/
structure Condition (F : Type) [FiniteField F] where
  witness (offset : ℕ) : (m : ℕ) → WitgenIR F m → Prop := fun _ _ => True
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

def Condition.implies (c c' : Condition F) : Condition F where
  witness n m compute := c.witness n m compute → c'.witness n m compute
  assert offset e := c.assert offset e → c'.assert offset e
  lookup offset l := c.lookup offset l → c'.lookup offset l
  interact offset i := c.interact offset i → c'.interact offset i
  subcircuit offset _ s := c.subcircuit offset s → c'.subcircuit offset s

structure ConditionNoOffset (F : Type) [FiniteField F] where
  witness (m : ℕ) (_ : WitgenIR F m) : Prop := True
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

@[circuit_norm]
theorem forAllNoOffset_empty {condition : ConditionNoOffset F} :
    forAllNoOffset condition [] = True := rfl

@[circuit_norm]
theorem forAllNoOffset_append {condition : ConditionNoOffset F} {as bs: Operations F} :
    forAllNoOffset condition (as ++ bs) ↔
      forAllNoOffset condition as ∧ forAllNoOffset condition bs := by
  induction as using induct with
  | empty => simp [forAllNoOffset]
  | witness _ _ _ ih | assert _ _ ih | lookup _ _ ih | subcircuit _ _ ih | interact _ _ ih =>
    simp only [List.cons_append, forAllNoOffset, ih, and_assoc]

lemma forAllNoOffset_iff_forall_mem {condition : ConditionNoOffset F} {ops : Operations F} :
  forAllNoOffset condition ops ↔
    (∀ e ∈ shallowConstraints ops, condition.assert e) ∧
    (∀ l ∈ shallowLookups ops, condition.lookup l) ∧
    (∀ i ∈ shallowInteractions ops, condition.interact i) ∧
    (∀ t ∈ shallowWitnessOperations ops, condition.witness t.1 t.2) ∧
    (∀ s ∈ subcircuits ops, condition.subcircuit s.2) := by
  induction ops using induct
  all_goals
  simp only [forAllNoOffset, shallowConstraints, shallowLookups, shallowInteractions,
    shallowWitnessOperations, subcircuits,
    List.mem_cons, or_imp, forall_and, forall_eq]
  tauto

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

/--
What it means that "constraints hold" on a sequence of operations.
- For assertions, the expression must evaluate to 0
- For lookups, the evaluated entry must be in the table
By using the full `constraints` and `lookups` here, we include constraints in subcircuits.
-/
@[circuit_norm]
def ConstraintsHold (env : Environment F) (ops : Operations F) : Prop :=
  (∀ e ∈ ops.constraints, env e = 0) ∧ (∀ l ∈ ops.lookups, l.Contains env)
end Operations

/-- Version of `ConstraintsHold` that replaces the statement of subcircuits with `Assumptions → Spec`. -/
@[circuit_norm]
def ConstraintsHold.Soundness (env : Environment F)
    (ops : Operations F) : Prop := ops.forAllNoOffset {
  assert e := env e = 0
  lookup l := l.Soundness env
  interact i := i.Guarantees env
  subcircuit s := s.Assumptions env → s.Spec env
}

/-- Version of `ConstraintsHold` that replaces the statement of subcircuits with their `ProverAssumptions`. -/
@[circuit_norm]
def ConstraintsHold.Completeness (env : ProverEnvironment F)
    (ops : Operations F) : Prop := ops.forAllNoOffset {
  assert e := env e = 0
  lookup l := l.Completeness env
  interact i := i.Guarantees env
  subcircuit s := s.ProverAssumptions env
}

lemma constraintsHold_soundness_iff_forall_mem {env : Environment F} {ops : Operations F} :
    ConstraintsHold.Soundness env ops ↔
    (∀ e ∈ ops.shallowConstraints, env e = 0) ∧
    (∀ l ∈ ops.shallowLookups, l.Soundness env) ∧
    (∀ i ∈ ops.shallowInteractions, i.Guarantees env) ∧
    (∀ s ∈ ops.subcircuits, s.2.Assumptions env → s.2.Spec env) := by
  simp [ConstraintsHold.Soundness, Operations.forAllNoOffset_iff_forall_mem]

lemma constraintsHold_completeness_iff_forall_mem {env : ProverEnvironment F} {ops : Operations F} :
    ConstraintsHold.Completeness env ops ↔
    (∀ e ∈ ops.shallowConstraints, env e = 0) ∧
    (∀ l ∈ ops.shallowLookups, l.Completeness env) ∧
    (∀ i ∈ ops.shallowInteractions, i.Guarantees env) ∧
    (∀ s ∈ ops.subcircuits, s.2.ProverAssumptions env) := by
  simp [ConstraintsHold.Completeness, Operations.forAllNoOffset_iff_forall_mem]

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

def subcircuitChannelsWithGuarantees (ops : Operations F) : List (RawChannel F) :=
  ops.map (fun
    | .subcircuit s => s.channelsWithGuarantees
    | .witness _ _ | .assert _ | .lookup _ | .interact _ => [])
  |> List.flatten

def subcircuitChannelsWithRequirements (ops : Operations F) : List (RawChannel F) :=
  ops.map (fun
    | .subcircuit s => s.channelsWithRequirements
    | .witness _ _ | .assert _ | .lookup _ | .interact _ => [])
  |> List.flatten

def shallowChannels (ops : Operations F) : List (RawChannel F) :=
  ops.map (fun
    | .interact i => [i.channel]
    | .subcircuit _ | .witness _ _ | .assert _ | .lookup _ => [])
  |>.flatten

def channels (ops : Operations F) : List (RawChannel F) := ops.interactions.map (·.channel)

-- TODO rename to ShallowGuarantees
@[circuit_norm]
def Guarantees (env : Environment F) (ops : Operations F) : Prop :=
  ops.forAllNoOffset { interact i := i.Guarantees env }

lemma guarantees_iff_forall_mem {env : Environment F} {ops : Operations F} :
    Guarantees env ops ↔
    ∀ i ∈ ops.shallowInteractions, i.Guarantees env := by
  simp [Guarantees, forAllNoOffset_iff_forall_mem]

@[circuit_norm]
def FullGuarantees (env : Environment F) (ops : Operations F) : Prop :=
  ∀ i ∈ ops.interactions, i.Guarantees env

-- TODO rename to ShallowRequirements
@[circuit_norm]
def Requirements (env : Environment F) (ops : Operations F) : Prop :=
  ops.forAllNoOffset {
    interact i := i.Requirements env
    subcircuit s := s.channelsWithRequirements = [] ∨ s.Assumptions env
  }

lemma requirements_iff_forall_mem {env : Environment F} {ops : Operations F} :
    Requirements env ops ↔
    (∀ i ∈ ops.shallowInteractions, i.Requirements env) ∧
    (∀ s ∈ ops.subcircuits, s.2.channelsWithRequirements = [] ∨ s.2.Assumptions env) := by
  simp [Requirements, forAllNoOffset_iff_forall_mem]

@[circuit_norm]
def FullRequirements (env : Environment F) (ops : Operations F) : Prop :=
  ∀ i ∈ ops.interactions, i.Requirements env

@[circuit_norm]
def ChannelGuarantees (channel : RawChannel F) (env : Environment F) (ops : Operations F) :=
  ∀ i ∈ ops.interactions, i.channel = channel → i.Guarantees env

@[circuit_norm]
def ChannelRequirements (channel : RawChannel F) (env : Environment F) (ops : Operations F) :=
  ∀ i ∈ ops.interactions, i.channel = channel → i.Requirements env

@[circuit_norm]
def InChannelsOrGuarantees (channels : List (RawChannel F)) (env : Environment F)
    (ops : Operations F) : Prop :=
  ops.forAllNoOffset { interact i := i.channel ∈ channels ∨ i.Guarantees env }

lemma inChannelsOrGuarantees_iff_forall_mem {channels : List (RawChannel F)} {env : Environment F} {ops : Operations F} :
    InChannelsOrGuarantees channels env ops ↔
    ∀ i ∈ ops.shallowInteractions, i.channel ∈ channels ∨ i.Guarantees env := by
  simp [InChannelsOrGuarantees, forAllNoOffset_iff_forall_mem]

theorem InChannelsOrGuarantees.mono {channels channels' : List (RawChannel F)}
    {env : Environment F} {ops : Operations F} :
    channels ⊆ channels' →
    ops.InChannelsOrGuarantees channels env →
    ops.InChannelsOrGuarantees channels' env := by
  intro h_subset h
  rw [inChannelsOrGuarantees_iff_forall_mem] at h ⊢
  intro i h_i
  rcases h i h_i with h_channel | h_guarantees
  · exact Or.inl (h_subset h_channel)
  · exact Or.inr h_guarantees

@[circuit_norm]
def InChannelsOrGuaranteesFull (channels : List (RawChannel F)) (env : Environment F) (ops : Operations F) : Prop :=
  ∀ i ∈ ops.interactions, i.channel ∈ channels ∨ i.Guarantees env

@[circuit_norm]
def InChannelsOrRequirements (channels : List (RawChannel F)) (env : Environment F)
    (ops : Operations F) : Prop :=
  ops.forAllNoOffset { interact i := i.channel ∈ channels ∨ i.Requirements env }

lemma inChannelsOrRequirements_iff_forall_mem {channels : List (RawChannel F)} {env : Environment F} {ops : Operations F} :
    InChannelsOrRequirements channels env ops ↔
    ∀ i ∈ ops.shallowInteractions, i.channel ∈ channels ∨ i.Requirements env := by
  simp [InChannelsOrRequirements, forAllNoOffset_iff_forall_mem]

theorem InChannelsOrRequirements.mono {channels channels' : List (RawChannel F)}
    {env : Environment F} {ops : Operations F} :
    channels ⊆ channels' →
    ops.InChannelsOrRequirements channels env →
    ops.InChannelsOrRequirements channels' env := by
  intro h_subset h
  rw [inChannelsOrRequirements_iff_forall_mem] at h ⊢
  intro i h_i
  rcases h i h_i with h_channel | h_requirements
  · exact Or.inl (h_subset h_channel)
  · exact Or.inr h_requirements

@[circuit_norm]
def InChannelsOrRequirementsFull (channels : List (RawChannel F)) (env : Environment F) (ops : Operations F) : Prop :=
  ∀ i ∈ ops.interactions, i.channel ∈ channels ∨ i.Requirements env
end Operations

namespace Operations
-- simp lemmas for suboperations

@[circuit_norm] lemma constraints_nil : constraints ([] : Operations F) = [] := rfl
@[circuit_norm] lemma constraints_assert (e : Expression F) (ops : Operations F) :
  constraints (.assert e :: ops) = e :: constraints ops := rfl
@[circuit_norm] lemma constraints_witness (m : ℕ) (c : WitgenIR F m) (ops : Operations F) :
  constraints (.witness m c :: ops) = constraints ops := rfl
@[circuit_norm] lemma constraints_lookup (l : Lookup F) (ops : Operations F) :
  constraints (.lookup l :: ops) = constraints ops := rfl
@[circuit_norm] lemma constraints_interact (i : AbstractInteraction F) (ops : Operations F) :
  constraints (.interact i :: ops) = constraints ops := rfl
@[circuit_norm] lemma constraints_subcircuit {n : ℕ} (s : Subcircuit F n) (ops : Operations F) :
  constraints (.subcircuit s :: ops) = FlatOperation.constraints s.ops.toFlat ++ constraints ops := rfl

@[circuit_norm] lemma constraints_append (ops1 ops2 : Operations F) :
    constraints (ops1 ++ ops2) = constraints ops1 ++ constraints ops2 := by
  induction ops1 using induct <;> simp_all [constraints]

@[circuit_norm] lemma lookups_nil : lookups ([] : Operations F) = [] := rfl
@[circuit_norm] lemma lookups_assert (e : Expression F) (ops : Operations F) :
  lookups (.assert e :: ops) = lookups ops := rfl
@[circuit_norm] lemma lookups_witness (m : ℕ) (c : WitgenIR F m) (ops : Operations F) :
  lookups (.witness m c :: ops) = lookups ops := rfl
@[circuit_norm] lemma lookups_lookup (l : Lookup F) (ops : Operations F) :
  lookups (.lookup l :: ops) = l :: lookups ops := rfl
@[circuit_norm] lemma lookups_interact (i : AbstractInteraction F) (ops : Operations F) :
  lookups (.interact i :: ops) = lookups ops := rfl
@[circuit_norm] lemma lookups_subcircuit {n : ℕ} (s : Subcircuit F n) (ops : Operations F) :
  lookups (.subcircuit s :: ops) = FlatOperation.lookups s.ops.toFlat ++ lookups ops := rfl

@[circuit_norm] lemma lookups_append (ops1 ops2 : Operations F) :
    lookups (ops1 ++ ops2) = lookups ops1 ++ lookups ops2 := by
  induction ops1 using induct <;> simp_all [lookups]

@[circuit_norm] lemma interactions_nil : interactions ([] : Operations F) = [] := rfl
@[circuit_norm] lemma interactions_assert (e : Expression F) (ops : Operations F) :
  interactions (.assert e :: ops) = interactions ops := rfl
@[circuit_norm] lemma interactions_witness (m : ℕ) (c : WitgenIR F m) (ops : Operations F) :
  interactions (.witness m c :: ops) = interactions ops := rfl
@[circuit_norm] lemma interactions_lookup (l : Lookup F) (ops : Operations F) :
  interactions (.lookup l :: ops) = interactions ops := rfl
@[circuit_norm] lemma interactions_interact (i : AbstractInteraction F) (ops : Operations F) :
  interactions (.interact i :: ops) = i :: interactions ops := rfl
@[circuit_norm] lemma interactions_subcircuit {n : ℕ} (s : Subcircuit F n) (ops : Operations F) :
  interactions (.subcircuit s :: ops) = FlatOperation.interactions s.ops.toFlat ++ interactions ops := rfl

@[circuit_norm] lemma interactions_append (ops1 ops2 : Operations F) :
    interactions (ops1 ++ ops2) = interactions ops1 ++ interactions ops2 := by
  induction ops1 using induct <;> simp_all [interactions]

@[circuit_norm] lemma shallowInteractions_nil : shallowInteractions ([] : Operations F) = [] := rfl
@[circuit_norm] lemma shallowInteractions_assert (e : Expression F) (ops : Operations F) :
  shallowInteractions (.assert e :: ops) = shallowInteractions ops := rfl
@[circuit_norm] lemma shallowInteractions_witness (m : ℕ) (c : WitgenIR F m) (ops : Operations F) :
  shallowInteractions (.witness m c :: ops) = shallowInteractions ops := rfl
@[circuit_norm] lemma shallowInteractions_lookup (l : Lookup F) (ops : Operations F) :
  shallowInteractions (.lookup l :: ops) = shallowInteractions ops := rfl
@[circuit_norm] lemma shallowInteractions_interact (i : AbstractInteraction F) (ops : Operations F) :
  shallowInteractions (.interact i :: ops) = i :: shallowInteractions ops := rfl
@[circuit_norm] lemma shallowInteractions_subcircuit {n : ℕ} (s : Subcircuit F n) (ops : Operations F) :
  shallowInteractions (.subcircuit s :: ops) = shallowInteractions ops := rfl

@[circuit_norm] lemma shallowInteractions_append (ops1 ops2 : Operations F) :
    shallowInteractions (ops1 ++ ops2) = shallowInteractions ops1 ++ shallowInteractions ops2 := by
  induction ops1 using induct <;> simp_all [shallowInteractions]

@[circuit_norm] lemma witnessOperations_nil : witnessOperations ([] : Operations F) = [] := rfl
@[circuit_norm] lemma witnessOperations_assert (e : Expression F) (ops : Operations F) :
  witnessOperations (.assert e :: ops) = witnessOperations ops := rfl
@[circuit_norm] lemma witnessOperations_witness (m : ℕ) (c : WitgenIR F m) (ops : Operations F) :
  witnessOperations (.witness m c :: ops) = ⟨m, c⟩ :: witnessOperations ops := rfl
@[circuit_norm] lemma witnessOperations_lookup (l : Lookup F) (ops : Operations F) :
  witnessOperations (.lookup l :: ops) = witnessOperations ops := rfl
@[circuit_norm] lemma witnessOperations_interact (i : AbstractInteraction F) (ops : Operations F) :
  witnessOperations (.interact i :: ops) = witnessOperations ops := rfl
@[circuit_norm] lemma witnessOperations_subcircuit {n : ℕ} (s : Subcircuit F n) (ops : Operations F) :
  witnessOperations (.subcircuit s :: ops) = FlatOperation.witnessOperations s.ops.toFlat ++ witnessOperations ops := rfl

@[circuit_norm] lemma witnessOperations_append (ops1 ops2 : Operations F) :
    witnessOperations (ops1 ++ ops2) = witnessOperations ops1 ++ witnessOperations ops2 := by
  induction ops1 using induct <;> simp_all [witnessOperations]

@[circuit_norm] lemma subcircuits_nil : subcircuits ([] : Operations F) = [] := rfl
@[circuit_norm] lemma subcircuits_assert (e : Expression F) (ops : Operations F) :
  subcircuits (.assert e :: ops) = subcircuits ops := rfl
@[circuit_norm] lemma subcircuits_witness (m : ℕ) (c : WitgenIR F m) (ops : Operations F) :
  subcircuits (.witness m c :: ops) = subcircuits ops := rfl
@[circuit_norm] lemma subcircuits_lookup (l : Lookup F) (ops : Operations F) :
  subcircuits (.lookup l :: ops) = subcircuits ops := rfl
@[circuit_norm] lemma subcircuits_interact (i : AbstractInteraction F) (ops : Operations F) :
  subcircuits (.interact i :: ops) = subcircuits ops := rfl
@[circuit_norm] lemma subcircuits_subcircuit {n : ℕ} (s : Subcircuit F n) (ops : Operations F) :
  subcircuits (.subcircuit s :: ops) = ⟨n, s⟩ :: subcircuits ops := rfl

@[circuit_norm] lemma subcircuits_append (ops1 ops2 : Operations F) :
    subcircuits (ops1 ++ ops2) = subcircuits ops1 ++ subcircuits ops2 := by
  induction ops1 using induct <;> simp_all [subcircuits]

theorem interactionsWith_append {channel : RawChannel F} {ops1 ops2 : Operations F} :
    interactionsWith channel (ops1 ++ ops2) =
      interactionsWith channel ops1 ++ interactionsWith channel ops2 := by
  simp [interactionsWith, interactions_append]

@[circuit_norm]
theorem subcircuitChannelsWithGuarantees_nil : subcircuitChannelsWithGuarantees ([] : Operations F) = [] := rfl
@[circuit_norm]
theorem subcircuitChannelsWithGuarantees_witness (m : ℕ) (c : WitgenIR F m) (ops : Operations F) :
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

lemma subcircuitChannelsWithGuarantees_eq_subcircuits_map {ops : Operations F} :
    subcircuitChannelsWithGuarantees ops = (ops.subcircuits.map (·.2.channelsWithGuarantees)).flatten := by
  induction ops using induct <;>
  simp_all [subcircuitChannelsWithGuarantees, Operations.subcircuits]

@[circuit_norm]
theorem subcircuitChannelsWithGuarantees_append (ops1 ops2 : Operations F) :
    subcircuitChannelsWithGuarantees (ops1 ++ ops2) =
      subcircuitChannelsWithGuarantees ops1 ++ subcircuitChannelsWithGuarantees ops2 := by
  simp [subcircuitChannelsWithGuarantees_eq_subcircuits_map, subcircuits_append]

lemma subcircuitChannelsWithGuarantees_subset_iff_forall {ops : Operations F} {channels : List (RawChannel F)} :
  subcircuitChannelsWithGuarantees ops ⊆ channels ↔
    ∀ s ∈ ops.subcircuits, ∀ c ∈ s.2.channelsWithGuarantees, c ∈ channels := by
  rw [subcircuitChannelsWithGuarantees_eq_subcircuits_map, List.subset_def]
  simp
  tauto

@[circuit_norm]
theorem subcircuitChannelsWithRequirements_nil : subcircuitChannelsWithRequirements ([] : Operations F) = [] := rfl
@[circuit_norm]
theorem subcircuitChannelsWithRequirements_witness (m : ℕ) (c : WitgenIR F m) (ops : Operations F) :
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

lemma subcircuitChannelsWithRequirements_eq_subcircuits_map {ops : Operations F} :
    subcircuitChannelsWithRequirements ops = (ops.subcircuits
    |>.map (fun s => s.2.channelsWithRequirements) |>.flatten) := by
  induction ops using induct <;>
  simp_all [subcircuitChannelsWithRequirements, Operations.subcircuits]

@[circuit_norm]
theorem subcircuitChannelsWithRequirements_append (ops1 ops2 : Operations F) :
    subcircuitChannelsWithRequirements (ops1 ++ ops2) =
      subcircuitChannelsWithRequirements ops1 ++ subcircuitChannelsWithRequirements ops2 := by
  simp [subcircuitChannelsWithRequirements_eq_subcircuits_map, subcircuits_append]

lemma subcircuitChannelsWithRequirements_subset_iff_forall {ops : Operations F} {channels : List (RawChannel F)} :
  subcircuitChannelsWithRequirements ops ⊆ channels ↔
    ∀ s ∈ ops.subcircuits, ∀ c ∈ s.2.channelsWithRequirements, c ∈ channels := by
  rw [subcircuitChannelsWithRequirements_eq_subcircuits_map, List.subset_def]
  simp
  tauto

@[circuit_norm] theorem shallowChannels_nil : shallowChannels ([] : Operations F) = [] := rfl
@[circuit_norm] theorem shallowChannels_witness (m : ℕ) (c : WitgenIR F m) (ops : Operations F) :
  shallowChannels (.witness m c :: ops) = shallowChannels ops := rfl
@[circuit_norm] theorem shallowChannels_assert (e : Expression F) (ops : Operations F) :
  shallowChannels (.assert e :: ops) = shallowChannels ops := rfl
@[circuit_norm] theorem shallowChannels_lookup (l : Lookup F) (ops : Operations F) :
  shallowChannels (.lookup l :: ops) = shallowChannels ops := rfl
@[circuit_norm] theorem shallowChannels_interact (i : AbstractInteraction F) (ops : Operations F) :
  shallowChannels (.interact i :: ops) = i.channel :: shallowChannels ops := rfl
@[circuit_norm] theorem shallowChannels_subcircuit {n : ℕ} (s : Subcircuit F n) (ops : Operations F) :
  shallowChannels (.subcircuit s :: ops) = shallowChannels ops := rfl

lemma shallowChannels_eq_interactions_map {ops : Operations F} :
    shallowChannels ops = ops.shallowInteractions.map (·.channel) := by
  induction ops using induct <;> simp_all [shallowInteractions, shallowChannels]

@[circuit_norm] theorem shallowChannels_append (ops1 ops2 : Operations F) :
    shallowChannels (ops1 ++ ops2) = shallowChannels ops1 ++ shallowChannels ops2 := by
  simp [shallowChannels_eq_interactions_map, shallowInteractions_append]

def SubcircuitChannelsLawful (ops : Operations F) : Prop :=
  ∀ s ∈ ops.subcircuits, s.2.ChannelsLawful

@[circuit_norm]
theorem subcircuitChannelsLawful_append (ops ops' : Operations F) :
    SubcircuitChannelsLawful (ops ++ ops') ↔ SubcircuitChannelsLawful ops ∧ SubcircuitChannelsLawful ops' := by
  simp [SubcircuitChannelsLawful, subcircuits_append, List.mem_append]
  grind

lemma subcircuitChannelsLawful_iff_forall {ops : Operations F} :
    ops.SubcircuitChannelsLawful ↔ ∀ s ∈ ops.subcircuits, s.2.ChannelsLawful := by rfl

@[circuit_norm]
lemma subcircuitChannelsLawful_iff_forAllNoOffset {ops : Operations F} :
  ops.SubcircuitChannelsLawful ↔
    ops.forAllNoOffset { subcircuit s := s.ChannelsLawful } := by
  simp [SubcircuitChannelsLawful, forAllNoOffset_iff_forall_mem]

def shallowChannelsWithGuarantees (ops : Operations F) : List (RawChannel F) :=
  (ops.shallowInteractions.filter (·.assumeGuarantees)).map (·.channel)

def shallowChannelsWithRequirements (ops : Operations F) : List (RawChannel F) :=
  (ops.shallowInteractions.filter fun i => !i.assumeGuarantees).map (·.channel)

/--
Property we require from a circuit that exposes three channel lists:
`channelsWithGuarantees`, `channelsWithRequirements`, and `exposedChannels`.
 -/
@[circuit_norm]
def ChannelsLawful (ops : Operations F)
    (channelsWithGuarantees channelsWithRequirements : List (RawChannel F)) : Prop :=
  -- The `channelsWithGuarantees` cover all interactions that add guarantees.
  ops.subcircuitChannelsWithGuarantees ⊆ channelsWithGuarantees ∧
  (∀ env, ops.InChannelsOrGuarantees channelsWithGuarantees env) ∧

  -- The `channelsWithRequirements` cover all interactions that add requirements.
  ops.subcircuitChannelsWithRequirements ⊆ channelsWithRequirements ∧
  (∀ env, ops.InChannelsOrRequirements channelsWithRequirements env) ∧

  -- Together, the two channel lists cover all interactions.
  -- Even if the conditions so far theoretically allow it, we must not leave out any channels
  -- we interacted with from the combination of both lists. This is because "did not interact
  -- with a given channel" is important knowledge during end-to-end proofs, when we need to prove
  -- that _all_ interactions with a given channel have some property.
  -- (If this ever becomes too restrictive for real circuits, we can relax by introducing a third
  -- list of "other channels".)
  (∀ channel ∈ ops.shallowChannels,
    channel ∈ channelsWithGuarantees ∨ channel ∈ channelsWithRequirements) ∧

  -- Every subcircuit used by this circuit exposes lawful channel metadata itself.
  ops.SubcircuitChannelsLawful

/-- Exposed channel interactions agree with the actual interactions in the circuit. -/
@[circuit_norm]
def ExposedChannelsLawful (ops : Operations F) (exposedChannels : List (ExposedChannel F)) : Prop :=
  (∀ exposed ∈ exposedChannels,
    ops.interactionsWith exposed.channel = exposed.interactions)

theorem channelsLawful_nil : ChannelsLawful ([] : Operations F) [] [] := by
  simp [ChannelsLawful, InChannelsOrGuarantees, InChannelsOrRequirements, SubcircuitChannelsLawful,
    subcircuitChannelsWithGuarantees, subcircuitChannelsWithRequirements, shallowChannels, subcircuits,
    forAllNoOffset]

theorem channelsLawful_append_of_channelsLawful {ops ops' : Operations F}
    {channelsWithGuarantees channelsWithGuarantees' channelsWithRequirements channelsWithRequirements' :
      List (RawChannel F)} :
    ops.ChannelsLawful channelsWithGuarantees channelsWithRequirements →
    ops'.ChannelsLawful channelsWithGuarantees' channelsWithRequirements' →
    (ops ++ ops').ChannelsLawful
      (channelsWithGuarantees ++ channelsWithGuarantees')
      (channelsWithRequirements ++ channelsWithRequirements') := by
  intro h h'
  dsimp only [ChannelsLawful] at h h' ⊢
  obtain ⟨h_g_subset, h_g, h_r_subset, h_r, h_shallow, h_sub⟩ := h
  obtain ⟨h_g_subset', h_g', h_r_subset', h_r', h_shallow', h_sub'⟩ := h'
  have append_subset_append {as bs cs ds : List (RawChannel F)}
      (h_as : as ⊆ cs) (h_bs : bs ⊆ ds) : as ++ bs ⊆ cs ++ ds := by
    intro channel h_channel
    rw [List.mem_append] at h_channel ⊢
    rcases h_channel with h_channel | h_channel
    · exact Or.inl (h_as h_channel)
    · exact Or.inr (h_bs h_channel)
  and_intros
  · rw [subcircuitChannelsWithGuarantees_append]
    exact append_subset_append h_g_subset h_g_subset'
  · intro env
    rw [InChannelsOrGuarantees, forAllNoOffset_append]
    exact ⟨h_g env |>.mono (List.subset_append_left _ _),
      h_g' env |>.mono (List.subset_append_right _ _)⟩
  · rw [subcircuitChannelsWithRequirements_append]
    exact append_subset_append h_r_subset h_r_subset'
  · intro env
    rw [InChannelsOrRequirements, forAllNoOffset_append]
    exact ⟨h_r env |>.mono (List.subset_append_left _ _),
      h_r' env |>.mono (List.subset_append_right _ _)⟩
  · rw [shallowChannels_append]
    intro channel h_channel
    rw [List.mem_append] at h_channel
    rcases h_channel with h_channel | h_channel
    · rcases h_shallow channel h_channel with h_channel | h_channel
      · exact Or.inl (List.mem_append_left _ h_channel)
      · exact Or.inr (List.mem_append_left _ h_channel)
    · rcases h_shallow' channel h_channel with h_channel | h_channel
      · exact Or.inl (List.mem_append_right _ h_channel)
      · exact Or.inr (List.mem_append_right _ h_channel)
  · rw [subcircuitChannelsLawful_append]
    exact ⟨h_sub, h_sub'⟩

@[circuit_norm]
def interactionValues (ops : Operations F)
    (env : Environment F) : List (Interaction F) :=
  ops.interactions.map (AbstractInteraction.eval env)

-- TODO this should probably be rewritten into an easily-simplifying form, for `FormalCircuit.exposedInteractions`
open Classical in
noncomputable def interactionValuesWith (channel : RawChannel F)
    (ops : Operations F) (env : Environment F) : List (Interaction F) :=
  ops.interactionsWith channel |>.map (·.eval env)

@[circuit_norm]
lemma interactionValuesWith_eq_map {channel : RawChannel F} {ops : Operations F} {env : Environment F} :
    ops.interactionValuesWith channel env = (ops.interactionsWith channel).map (·.eval env) := rfl

open Classical in
lemma interactionValuesWith_eq_filter {channel : RawChannel F} {ops : Operations F} {env : Environment F} :
    ops.interactionValuesWith channel env = (ops.interactionValues env).filter (·.channel = channel) := by
  simp only [interactionValuesWith, interactionsWith, interactionValues, List.filter_map]
  rfl

lemma channel_eq_of_mem_interactionsWith {channel : RawChannel F} {ops : Operations F}
  {i : AbstractInteraction F} :
    i ∈ ops.interactionsWith channel → i.channel = channel := by
  simp_all [interactionsWith]

@[circuit_norm]
lemma forall_interactionsWith_iff {channel : RawChannel F} {ops : Operations F}
  {motive : AbstractInteraction F → Prop} :
    (∀ i ∈ ops.interactionsWith channel, motive i) ↔
    (∀ i ∈ ops.interactions, i.channel = channel → motive i) := by
  simp [interactionsWith]

@[circuit_norm] lemma toFlat_nil : toFlat ([] : Operations F) = [] := rfl
@[circuit_norm] lemma toFlat_witness (m : ℕ) (c : WitgenIR F m) (ops : Operations F) :
  toFlat (.witness m c :: ops) = .witness m c :: toFlat ops := rfl
@[circuit_norm] lemma toFlat_assert (e : Expression F) (ops : Operations F) :
  toFlat (.assert e :: ops) = .assert e :: toFlat ops := rfl
@[circuit_norm] lemma toFlat_lookup (l : Lookup F) (ops : Operations F) :
  toFlat (.lookup l :: ops) = .lookup l :: toFlat ops := rfl
@[circuit_norm] lemma toFlat_interact (i : AbstractInteraction F) (ops : Operations F) :
  toFlat (.interact i :: ops) = .interact i :: toFlat ops := rfl
@[circuit_norm] lemma toFlat_subcircuit {n : ℕ} (s : Subcircuit F n) (ops : Operations F) :
  toFlat (.subcircuit s :: ops) = s.ops.toFlat ++ toFlat ops := rfl

@[circuit_norm] lemma witnessOperations_toFlat {ops : Operations F} :
    FlatOperation.witnessOperations ops.toFlat = ops.witnessOperations := by
  induction ops using Operations.induct <;>
  simp_all [circuit_norm, FlatOperation.witnessOperations]

@[circuit_norm] lemma constraints_toFlat {ops : Operations F} :
    FlatOperation.constraints ops.toFlat = ops.constraints := by
  induction ops using Operations.induct <;>
  simp_all [circuit_norm, FlatOperation.constraints]

@[circuit_norm] lemma lookups_toFlat {ops : Operations F} :
    FlatOperation.lookups ops.toFlat = ops.lookups := by
  induction ops using Operations.induct <;>
  simp_all [circuit_norm, FlatOperation.lookups]

@[circuit_norm] lemma interactions_toFlat {ops : Operations F} :
    FlatOperation.interactions ops.toFlat = ops.interactions := by
  induction ops using Operations.induct <;>
  simp_all [circuit_norm, FlatOperation.interactions]

@[circuit_norm] lemma channels_toFlat {ops : Operations F} :
    FlatOperation.channels ops.toFlat = ops.channels := by
  simp [channels, FlatOperation.channels, interactions_toFlat]

@[circuit_norm]
theorem append_localLength {a b: Operations F} :
    (a ++ b).localLength = a.localLength + b.localLength := by
  induction a using induct with
  | empty => ac_rfl
  | witness _ _ _ ih | assert _ _ ih | lookup _ _ ih | subcircuit _ _ ih | interact _ _ ih =>
    simp_all +arith [localLength]

@[circuit_norm]
theorem forAll_empty {condition : Condition F} {n : ℕ} : forAll n condition [] = True := rfl

@[circuit_norm]
theorem forAll_append {condition : Condition F} {offset : ℕ} {as bs: Operations F} :
  forAll offset condition (as ++ bs) ↔
    forAll offset condition as ∧ forAll (as.localLength + offset) condition bs := by
  induction as using induct generalizing offset with
  | empty => simp [forAll_empty, localLength]
  | witness _ _ _ ih | assert _ _ ih | lookup _ _ ih | subcircuit _ _ ih | interact _ _ ih =>
    simp +arith only [List.cons_append, forAll, localLength, ih, and_assoc]

theorem localLength_cons {a : Operation F} {as : Operations F} :
    localLength (a :: as) = a.localLength + as.localLength := by
  cases a <;> simp_all [localLength, Operation.localLength]

theorem localWitnesses_cons (op : Operation F) (ops : Operations F) (env : ProverEnvironment F) :
  localWitnesses env (op :: ops) =
    (op.localWitnesses env ++ ops.localWitnesses env).cast (localLength_cons.symm) := by
  cases op <;> simp only [localWitnesses, Operation.localWitnesses, Vector.cast_rfl]
  all_goals (try (rw [Vector.empty_append]; simp))

@[circuit_norm]
theorem forAll_cons {condition : Condition F} {offset : ℕ} {op : Operation F} {ops : Operations F} :
  forAll offset condition (op :: ops) ↔
    condition.apply offset op ∧ forAll (op.localLength + offset) condition ops := by
  cases op <;> simp [forAll, Operation.localLength, Condition.apply]

end Operations
