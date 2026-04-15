/-
Playground for channels using Fibonacci8 as an example

Goal - use three channels:
- a "bytes" channel that enables range checks using lookups into a table containing 0,...,255
- an "add8" channel that implements 8-bit addition as a standalone "chip" / table
- a "fibonacci" channel that that maintains state of the fibonacci table

Prove e2e soundness and completeness of the table ensemble.
-/
import Clean.Circuit
import Clean.Circuit.Extensions
import Clean.Gadgets.Addition8.Theorems
open ByteUtils (mod256 floorDiv256)
open Gadgets.Addition8 (Theorems.soundness Theorems.completeness_bool Theorems.completeness_add)

section
variable {F : Type} [Field F] [DecidableEq F]
variable {Input Output Message : TypeMap} [ProvableType Input] [ProvableType Output] [ProvableType Message]

-- TODO should we encode the channel width in the type, or not?
-- if not, we have trouble passing interactions to channel.Guarantees / Requirements
-- => but that doesn't really matter, we can always do (i.channel = channel) → i.Guarantees ...
-- if we do, we have to define a channel filtering mechanism that establishes the output type
structure Interaction (F : Type) where
  channel : RawChannel F
  mult : F
  msg : Array F
  same_size : msg.size = channel.arity
  assumeGuarantees : Bool

namespace Interaction
def msgVector (i : Interaction F) : Vector F i.channel.arity :=
  ⟨ i.msg, i.same_size ⟩

omit [Field F] [DecidableEq F] in
lemma msgVector_eq_iff_msg_eq_toArray
    {channel : RawChannel F} {i : Interaction F} {msg : Vector F channel.arity}
    (h : i.channel = channel) :
    h ▸ i.msgVector = msg ↔ i.msg = msg.toArray := by
  cases h
  cases msg
  simp [Interaction.msgVector]

def Guarantees (i : Interaction F) (data : ProverData F) : Prop :=
  i.assumeGuarantees → i.channel.Guarantees i.mult i.msgVector data

def Requirements (i : Interaction F) (data : ProverData F) : Prop :=
  i.channel.Requirements i.mult i.msgVector data
end Interaction

def AbstractInteraction.eval (env : Environment F) (i : AbstractInteraction F) : Interaction F where
  channel := i.channel
  mult := env i.mult
  msg := (i.msg.map env).toArray
  same_size := by simp
  assumeGuarantees := i.assumeGuarantees

omit [DecidableEq F] in @[circuit_norm]
lemma AbstractInteraction.eval_channel {i : AbstractInteraction F} {env : Environment F} :
  (i.eval env).channel = i.channel := rfl

omit [DecidableEq F] in @[circuit_norm]
lemma AbstractInteraction.eval_guarantees {i : AbstractInteraction F} {env : Environment F} :
    (i.eval env).Guarantees env.data ↔ i.Guarantees env := by
  simp only [Interaction.Guarantees, AbstractInteraction.eval, AbstractInteraction.Guarantees]
  rfl

omit [DecidableEq F] in @[circuit_norm]
lemma AbstractInteraction.eval_requirements {i : AbstractInteraction F} {env : Environment F} :
    (i.eval env).Requirements env.data ↔ i.Requirements env := by
  simp only [Interaction.Requirements, AbstractInteraction.eval, AbstractInteraction.Requirements]
  rfl

@[circuit_norm]
def Operations.interactionValues (ops : Operations F)
    (env : Environment F) : List (Interaction F) :=
  ops.interactions.map (AbstractInteraction.eval env)

-- TODO this should probably be rewritten into an easily-simplifying form, for `FormalCircuit.exposedInteractions`
open Classical in
@[circuit_norm]
noncomputable def Operations.interactionValuesWith (channel : RawChannel F)
    (ops : Operations F) (env : Environment F) : List (Interaction F) :=
  ops.interactionsWith channel |>.map (·.eval env)

omit [DecidableEq F] in
lemma Operations.interactionValuesWith_eq_map {channel : RawChannel F} {ops : Operations F} {env : Environment F} :
    ops.interactionValuesWith channel env = (ops.interactionsWith channel).map (·.eval env) := rfl

omit [DecidableEq F] in open Classical in
lemma Operations.interactionValuesWith_eq_filter {channel : RawChannel F} {ops : Operations F} {env : Environment F} :
    ops.interactionValuesWith channel env = (ops.interactionValues env).filter (·.channel = channel) := by
  simp only [interactionValuesWith, interactionsWith, interactionValues, List.filter_map]
  rfl

omit [DecidableEq F] in
lemma Operations.channel_eq_of_mem_interactionsWith {channel : RawChannel F} {ops : Operations F}
  {i : AbstractInteraction F} :
    i ∈ ops.interactionsWith channel → i.channel = channel := by
  simp_all [interactionsWith]

omit [DecidableEq F] in
@[circuit_norm]
lemma Operations.forall_interactionsWith_iff {channel : RawChannel F} {ops : Operations F}
  {motive : AbstractInteraction F → Prop} :
    (∀ i ∈ ops.interactionsWith channel, motive i) ↔
    (∀ i ∈ ops.interactions, i.channel = channel → motive i) := by
  simp [interactionsWith]

omit [DecidableEq F] in
@[circuit_norm]
theorem witnessAny_interactionsWith {n : ℕ} {channel : RawChannel F} :
    (witnessAny Message |>.operations n).interactionsWith channel = [] := by
  simp [circuit_norm, witnessAny, valueFromOffset, ProvableType.toElements_fromElements,
    Operations.interactionsWith]

namespace Channel
@[circuit_norm]
def pulledValue (channel : Channel F Message) (msg : Message F) : Interaction F where
  channel := channel.toRaw
  mult := -1
  msg := (toElements msg).toArray
  same_size := by simp [Channel.toRaw]
  assumeGuarantees := true

@[circuit_norm]
def pushedValue (channel : Channel F Message) (msg : Message F) : Interaction F where
  channel := channel.toRaw
  mult := 1
  msg := (toElements msg).toArray
  same_size := by simp [Channel.toRaw]
  assumeGuarantees := false

omit [DecidableEq F] in
lemma eval_pulled {channel : Channel F Message} {msg : Message (Expression F)} {env : Environment F} :
     (channel.pulled msg).toRaw.eval env = channel.pulledValue (eval env msg) := by
  simp only [circuit_norm, AbstractInteraction.eval, Interaction.mk.injEq]
  congr
  rw [←ProvableType.fromElements_eq_iff]
  rfl

omit [DecidableEq F] in
lemma eval_pushed {channel : Channel F Message} {msg : Message (Expression F)} {env : Environment F} :
     (channel.pushed msg).toRaw.eval env = channel.pushedValue (eval env msg) := by
  simp only [circuit_norm, AbstractInteraction.eval, Interaction.mk.injEq]
  congr
  rw [←ProvableType.fromElements_eq_iff]
  rfl
end Channel

/-- Lookup-like channels expose a predicate via both requirements and guarantees. -/
structure StaticLookupChannel (F : Type) [Field F] [DecidableEq F] (Message : TypeMap) [ProvableType Message] where
  name : String
  table : List (Message F)
  Guarantees : Message F → Prop
  guarantees_iff : ∀ msg, Guarantees msg ↔ msg ∈ table

@[circuit_norm]
def Channel.fromStatic (F : Type) [Field F] [DecidableEq F]
    (Message : TypeMap) [ProvableType Message]
    (slc : StaticLookupChannel F Message) : Channel F Message where
  name := slc.name
  Guarantees mult msg _ := mult = -1 → slc.Guarantees msg
  Requirements mult msg _ := mult ≠ -1 → slc.Guarantees msg

abbrev StaticLookupChannel.toChannel (slc : StaticLookupChannel F Message) :=
  Channel.fromStatic F Message slc

-- define what global soundness means for an ensemble of circuits/tables and channels

-- table contains the concrete values on which we expect constraints to hold
-- which also defines what concrete interactions are contained in each channel

-- tables need to be instantiated with a concrete circuit, not a family of circuits
-- this is achieved for any FormalCircuit* by witnessing the inputs and plugging them in

namespace FormalCircuitWithInteractions
@[circuit_norm]
def instantiate (circuit : FormalCircuitWithInteractions F Input Output) : Circuit F Unit := do
  let input ← witnessAny Input
  let _ ← circuit input -- we don't care about the output in this context

@[circuit_norm]
def instantiateConst (circuit : FormalCircuitWithInteractions F Input unit) (input : Input F) : Circuit F Unit := do
  let _ ← circuit (const input)

def instantiateConst_toFormal (circuit : FormalCircuitWithInteractions F Input unit) (input : Input F) :
    FormalCircuitWithInteractions F unit unit where
  main _ := circuit.instantiateConst input
  localLength _ := circuit.localLength (const input)
  output _ _ := ()
  Assumptions _ := circuit.Assumptions input
  Spec _ _ := circuit.Spec input ()
  channelsWithGuarantees := circuit.channelsWithGuarantees
  channelsWithRequirements := circuit.channelsWithRequirements
  soundness := by circuit_proof_all
  completeness := by circuit_proof_all

@[circuit_norm]
lemma instantiateConst_toFormal_operations {circuit : FormalCircuitWithInteractions F Input unit} {input : Input F} {n : ℕ} :
  ((circuit.instantiateConst_toFormal input).main ()).operations n =
    (circuit (const input)).operations n := rfl

def size (circuit : FormalCircuitWithInteractions F Input Output) : ℕ :=
  circuit.instantiate.localLength 0

lemma size_eq (circuit : FormalCircuitWithInteractions F Input Output) :
  circuit.size = (ProvableType.size Input) + circuit.localLength (varFromOffset Input 0) := rfl

def empty (F : Type) [Field F] [DecidableEq F] (Input : TypeMap) [ProvableType Input] :
    FormalCircuitWithInteractions F Input unit where
  main _ := return
  localLength _ := 0
  output _ _ := ()
  Assumptions | _, _ => True
  Spec _ _ _ := True
  soundness := by circuit_proof_start
  completeness := by circuit_proof_start

@[circuit_norm] lemma empty_operations : ∀ input n,
    ((empty F Input).main input).operations n = [] := by
  simp only [circuit_norm, empty]

@[circuit_norm] lemma empty_channelsWithGuarantees :
  (empty F Input).channelsWithGuarantees = [] := rfl

@[circuit_norm] lemma empty_channelsWithRequirements :
  (empty F Input).channelsWithRequirements = [] := rfl

end FormalCircuitWithInteractions

structure AbstractTable (F : Type) [Field F] [DecidableEq F] where
  {Input : TypeMap} {Output : TypeMap}
  [provableInput : ProvableType Input] [provableOutput : ProvableType Output]
  circuit : FormalCircuitWithInteractions F Input Output

instance (t: AbstractTable F) : ProvableType t.Input := t.provableInput
instance (t: AbstractTable F) : ProvableType t.Output := t.provableOutput

namespace AbstractTable
def operations (table : AbstractTable F) : Operations F :=
  table.circuit.instantiate.operations 0

def width (table : AbstractTable F) : ℕ := table.circuit.size

@[circuit_norm]
abbrev rowOffset (table : AbstractTable F) : ℕ := size table.Input
@[circuit_norm]
abbrev rowInputVar (table : AbstractTable F): Var table.Input F :=
  varFromOffset table.Input 0

/-- first `size Input` elements of the environment are the input -/
@[circuit_norm]
def rowInput (table : AbstractTable F) (row : Environment F) : table.Input F :=
  valueFromOffset table.Input 0 row

/-- output is whatever the circuit computes on the row input -/
@[circuit_norm]
def rowOutput (table : AbstractTable F) (row : Environment F) : table.Output F :=
  let outputVar := (table.circuit table.rowInputVar).output table.rowOffset
  eval row outputVar

@[circuit_norm]
def rowOperations (table : AbstractTable F) : Operations F :=
  table.circuit.main (varFromOffset table.Input 0) |>.operations (size table.Input)

def Spec (table : AbstractTable F) (row : Environment F) : Prop :=
  table.circuit.Spec (table.rowInput row) (table.rowOutput row) row

abbrev exposedChannels (table : AbstractTable F) : List (ExposedChannel F) :=
  table.circuit.exposedChannels table.rowInputVar table.rowOffset

variable {table : AbstractTable F} {env : Environment F}

lemma constraints_eq : table.operations.constraints = table.rowOperations.constraints := by
  simp only [circuit_norm, witnessAny, FormalCircuitWithInteractions.instantiate, AbstractTable.operations,
    FormalCircuitWithInteractions.toSubcircuit, Operations.constraints_toFlat]

lemma lookups_eq : table.operations.lookups = table.rowOperations.lookups := by
  simp only [circuit_norm, witnessAny, FormalCircuitWithInteractions.instantiate, AbstractTable.operations,
    FormalCircuitWithInteractions.toSubcircuit, Operations.lookups_toFlat]

lemma interactions_eq : table.operations.interactions = table.rowOperations.interactions := by
  simp only [circuit_norm, witnessAny, FormalCircuitWithInteractions.instantiate, AbstractTable.operations,
    FormalCircuitWithInteractions.toSubcircuit, Operations.interactions_toFlat]

lemma interactionsWith_eq {channel : RawChannel F} :
    table.operations.interactionsWith channel = table.rowOperations.interactionsWith channel := by
  simp only [Operations.interactionsWith, interactions_eq]

lemma interactionsValues_eq : table.operations.interactionValues env = table.rowOperations.interactionValues env := by
  simp only [Operations.interactionValues, interactions_eq]

lemma constraintsHold_iff (env : Environment F) :
    table.operations.ConstraintsHold env ↔ table.rowOperations.ConstraintsHold env := by
  simp only [circuit_norm, lookups_eq, constraints_eq]

lemma guarantees_iff (env : Environment F) :
    table.operations.FullGuarantees env ↔ table.rowOperations.FullGuarantees env := by
  simp only [circuit_norm, interactions_eq]

lemma requirements_iff (env : Environment F) :
    table.operations.FullRequirements env ↔ table.rowOperations.FullRequirements env := by
  simp only [circuit_norm, interactions_eq]

lemma channelGuarantees_iff (env : Environment F) (channel : RawChannel F) :
    table.operations.ChannelGuarantees channel env ↔ table.rowOperations.ChannelGuarantees channel env := by
  simp only [circuit_norm, interactions_eq]

lemma channelRequirements_iff (env : Environment F) (channel : RawChannel F) :
    table.operations.ChannelRequirements channel env ↔ table.rowOperations.ChannelRequirements channel env := by
  simp only [circuit_norm, interactions_eq]

lemma inChannelsOrRequirements (env : Environment F) :
    table.operations.InChannelsOrRequirementsFull table.circuit.channelsWithRequirements env := by
  have h := table.circuit.in_channels_or_requirements_full
  simp only [circuit_norm, interactions_eq] at *
  convert h _ _ env

lemma inChannelsOrGuarantees (env : Environment F) :
    table.operations.InChannelsOrGuaranteesFull table.circuit.channelsWithGuarantees env := by
  have h := table.circuit.in_channels_or_guarantees_full
  simp only [circuit_norm, interactions_eq] at *
  convert h _ _ env

-- this is the circuit's soundness theorem, stated in "instantiated" form
theorem weakSoundness {table : AbstractTable F} {env : Environment F} :
    table.operations.ConstraintsHold env →
    table.operations.FullGuarantees env →
      table.Spec env ∧ table.operations.FullRequirements env := by
  simp only [constraintsHold_iff, guarantees_iff, requirements_iff, rowOperations, Spec]
  intro h_constraints h_guarantees
  set inputVar := varFromOffset table.Input 0
  set ops := (table.circuit.main inputVar).operations (size table.Input)
  convert table.circuit.original_full_soundness _ _ _ h_constraints h_guarantees
  simp only [rowInput, eval_varFromOffset_valueFromOffset, inputVar]

end AbstractTable

structure TableWitness (F : Type) [Field F] [DecidableEq F] where
  abstract : AbstractTable F
  width : ℕ
  table : List (Array F)
  data : ProverData F
  uniform_width : ∀ row ∈ table, row.size = width

@[circuit_norm] abbrev Environment.fromArray (row : Array F) (data : ProverData F) : Environment F where
  get j := row[j]?.getD 0
  data
  interactions := [] -- I think we can remove this field??

abbrev Environment.fromInput (row : Message F) (data : ProverData F) : Environment F :=
  Environment.fromArray (toElements row).toArray data

omit [DecidableEq F] in @[circuit_norm]
lemma ProvableType.eval_fromInput_varFromOffset_zero
  (input : Message F) (data : ProverData F) :
    eval (.fromInput input data) (varFromOffset Message 0) = input := by
  simp only [Environment.fromInput, eval_varFromOffset]
  rw [ProvableType.fromElements_eq_iff, Vector.ext_iff]
  intro i hi
  rw [Vector.getElem_mapRange, zero_add, Vector.getElem?_toArray,
    Vector.getElem?_eq_getElem hi, Option.getD_some]

namespace TableWitness
variable {witness :TableWitness F} {channel : RawChannel F}

abbrev length (t : TableWitness F) : ℕ := t.table.length

def environment (witness : TableWitness F) (row : Array F) :=
  Environment.fromArray row witness.data

theorem ext_iff {witness1 witness2 : TableWitness F} :
    witness1 = witness2 ↔
    witness1.abstract = witness2.abstract ∧
    witness1.width = witness2.width ∧
    witness1.table = witness2.table ∧
    witness1.data = witness2.data := by
  cases witness1
  cases witness2
  simp only [mk.injEq]

@[circuit_norm]
def channelsWithGuarantees (witness : TableWitness F) : List (RawChannel F) :=
  witness.abstract.circuit.channelsWithGuarantees

@[circuit_norm]
def channelsWithRequirements (witness : TableWitness F) : List (RawChannel F) :=
  witness.abstract.circuit.channelsWithRequirements

def Constraints (witness : TableWitness F) : Prop :=
  ∀ row ∈ witness.table,
    witness.abstract.operations.ConstraintsHold (witness.environment row)

def Guarantees (witness : TableWitness F) : Prop :=
  ∀ row ∈ witness.table,
    witness.abstract.operations.FullGuarantees (witness.environment row)

def ChannelGuarantees (witness : TableWitness F) (channel : RawChannel F) : Prop :=
  ∀ row ∈ witness.table,
    witness.abstract.operations.ChannelGuarantees channel (witness.environment row)

def InChannelsOrGuarantees (witness : TableWitness F) (channels : List (RawChannel F)) : Prop :=
  ∀ row ∈ witness.table,
    witness.abstract.operations.InChannelsOrGuaranteesFull channels (witness.environment row)

def Requirements (witness : TableWitness F) : Prop :=
  ∀ row ∈ witness.table,
    witness.abstract.operations.FullRequirements (witness.environment row)

def ChannelRequirements (witness : TableWitness F) (channel : RawChannel F) : Prop :=
  ∀ row ∈ witness.table,
    witness.abstract.operations.ChannelRequirements channel (witness.environment row)

def InChannelsOrRequirements (witness : TableWitness F) (channels : List (RawChannel F)) : Prop :=
  ∀ row ∈ witness.table,
    witness.abstract.operations.InChannelsOrRequirementsFull channels (witness.environment row)

def Spec (witness : TableWitness F) : Prop :=
  ∀ row ∈ witness.table,
    witness.abstract.Spec (witness.environment row)

def interactions (witness : TableWitness F) : List (Interaction F) :=
  witness.table.flatMap fun row =>
    witness.abstract.operations.interactionValues (witness.environment row)

noncomputable def interactionsWith (witness : TableWitness F) (channel : RawChannel F) : List (Interaction F) :=
  witness.table.flatMap fun row =>
    witness.abstract.operations.interactionValuesWith channel (witness.environment row)

open Classical in
lemma interactionsWith_eq_filter :
    witness.interactionsWith channel = witness.interactions.filter (·.channel = channel) := by
  simp only [interactionsWith, interactions, List.filter_flatMap]
  congr
  funext row
  rw [Operations.interactionValuesWith_eq_filter]

lemma channel_eq_of_mem_interactionsWith {i : Interaction F} :
    i ∈ witness.interactionsWith channel → i.channel = channel := by
  intro h_mem
  simp only [interactionsWith, List.mem_flatMap] at h_mem
  rcases h_mem with ⟨row, h_row, hi⟩
  simp only [Operations.interactionValuesWith, List.mem_map] at hi
  rcases hi with ⟨i_abs, hi_abs, heq⟩
  rw [←heq]
  apply Operations.channel_eq_of_mem_interactionsWith hi_abs

lemma forall_interactions_iff (witness : TableWitness F) (motive : Interaction F → Prop) :
    (∀ i ∈ witness.interactions, motive i) ↔
    ∀ row ∈ witness.table, ∀ i ∈ witness.abstract.operations.interactions,
      motive (i.eval (witness.environment row)) := by
  simp only [interactions, Operations.interactionValues, List.mem_flatMap, List.mem_map,
    forall_exists_index, and_imp]
  constructor
  · intro h row h_row i hi
    set env := witness.environment row
    exact h (i.eval env) row h_row i hi rfl
  · intro h i row h_row i' hi' h_eq
    rw [← h_eq]
    exact h row h_row i' hi'

lemma forall_interactionsWith_iff (witness : TableWitness F) (channel : RawChannel F)
  (motive : Interaction F → Prop) :
    (∀ i ∈ witness.interactionsWith channel, motive i) ↔
    ∀ row ∈ witness.table, ∀ i ∈ witness.abstract.operations.interactions,
      (i.channel = channel → motive (i.eval (witness.environment row))) := by
  simp only [interactionsWith, List.mem_flatMap, List.mem_map,
    forall_exists_index, and_imp, circuit_norm]
  constructor
  · intro h row h_row i hi h_channel
    set env := witness.environment row
    exact h (i.eval env) row h_row i hi h_channel rfl
  · intro h i row h_row i' hi' h_channel h_eq
    rw [← h_eq]
    exact h row h_row i' hi' h_channel

lemma interactionsWith_nil_of_channel_not_mem :
    channel ∉ witness.abstract.circuit.channels → witness.interactionsWith channel = [] := by
  contrapose!
  simp only [AbstractInteraction.eval_channel, interactionsWith_eq_filter, ne_eq, List.filter_eq_nil_iff,
    decide_eq_true_eq, forall_interactions_iff, not_forall, not_not, forall_exists_index]
  intro table table_mem i i_mem channel_eq
  symm at channel_eq; subst channel_eq
  simp only [AbstractTable.interactions_eq] at i_mem
  apply witness.abstract.circuit.channels_subset
  simp only [Operations.channels, List.mem_map]
  exists i

lemma guarantees_iff_forall (witness : TableWitness F) :
    witness.Guarantees ↔
    ∀ i ∈ witness.interactions, i.Guarantees witness.data := by
  simp only [TableWitness.Guarantees, circuit_norm, forall_interactions_iff]
  rfl

lemma channelGuarantees_iff_forall (witness : TableWitness F) (channel : RawChannel F) :
    witness.ChannelGuarantees channel ↔
    ∀ i ∈ witness.interactionsWith channel, i.Guarantees witness.data := by
  simp only [TableWitness.ChannelGuarantees, circuit_norm, forall_interactionsWith_iff]
  rfl

lemma guarantees_iff_channelGuarantees (witness : TableWitness F) :
    witness.Guarantees ↔
    ∀ channel ∈ witness.channelsWithGuarantees, witness.ChannelGuarantees channel := by
  simp only [TableWitness.Guarantees, TableWitness.ChannelGuarantees, channelsWithGuarantees]
  simp only [AbstractTable.guarantees_iff, AbstractTable.channelGuarantees_iff, AbstractTable.rowOperations]
  simp only [FormalCircuitWithInteractions.guarantees_iff']
  constructor <;> simp_all

lemma channelGuarantees_of_requirements (witness : TableWitness F) {channel : RawChannel F} :
    witness.Guarantees → witness.ChannelGuarantees channel := by
  simp_all [TableWitness.Guarantees, TableWitness.ChannelGuarantees, circuit_norm]

lemma requirements_iff_forall (witness : TableWitness F) :
    witness.Requirements ↔
    ∀ i ∈ witness.interactions, i.Requirements witness.data := by
  simp only [TableWitness.Requirements, circuit_norm, forall_interactions_iff]
  rfl

lemma channelRequirements_iff_forall (witness : TableWitness F) (channel : RawChannel F) :
    witness.ChannelRequirements channel ↔
    ∀ i ∈ witness.interactionsWith channel, i.Requirements witness.data := by
  simp only [TableWitness.ChannelRequirements, circuit_norm, forall_interactionsWith_iff]
  rfl

lemma requirements_iff_channelRequirements (witness : TableWitness F) :
    witness.Requirements ↔
    ∀ channel ∈ witness.channelsWithRequirements, witness.ChannelRequirements channel := by
  simp only [TableWitness.Requirements, TableWitness.ChannelRequirements, channelsWithRequirements]
  simp only [AbstractTable.requirements_iff, AbstractTable.channelRequirements_iff, AbstractTable.rowOperations]
  simp only [FormalCircuitWithInteractions.requirements_iff']
  constructor <;> simp_all

lemma channelRequirements_of_requirements (witness : TableWitness F) {channel : RawChannel F} :
    witness.Requirements → witness.ChannelRequirements channel := by
  simp_all [TableWitness.Requirements, TableWitness.ChannelRequirements, circuit_norm]

lemma inChannelsOrRequirements (witness : TableWitness F) :
    witness.InChannelsOrRequirements witness.channelsWithRequirements := by
  simp [InChannelsOrRequirements, channelsWithRequirements, AbstractTable.inChannelsOrRequirements]

lemma requirements_of_not_mem (witness : TableWitness F) {channel : RawChannel F} :
    channel ∉ witness.channelsWithRequirements → witness.ChannelRequirements channel := by
  intro h_not_mem
  have h_in_or_req := witness.inChannelsOrRequirements
  simp only [ChannelRequirements, InChannelsOrRequirements] at *
  intro row h_row
  specialize h_in_or_req row h_row
  apply Operations.requirements_of_not_mem _ witness.channelsWithRequirements
  assumption
  assumption

lemma inChannelsOrGuarantees (witness : TableWitness F) :
    witness.InChannelsOrGuarantees witness.channelsWithGuarantees := by
  simp [InChannelsOrGuarantees, channelsWithGuarantees, AbstractTable.inChannelsOrGuarantees]

lemma guarantees_of_not_mem (witness : TableWitness F) {channel : RawChannel F} :
    channel ∉ witness.channelsWithGuarantees → witness.ChannelGuarantees channel := by
  intro h_not_mem
  have h_in_or_guar := witness.inChannelsOrGuarantees
  simp only [ChannelGuarantees, InChannelsOrGuarantees] at *
  intro row h_row
  specialize h_in_or_guar row h_row
  apply Operations.guarantees_of_not_mem _ witness.channelsWithGuarantees
  assumption
  assumption

/-- Circuit soundness, lifted to full table level --/
theorem weakSoundness {witness : TableWitness F} :
    witness.Constraints → witness.Guarantees → witness.Spec ∧ witness.Requirements := by
  simp_all [TableWitness.Constraints, TableWitness.Guarantees, TableWitness.Spec,
    TableWitness.Requirements, AbstractTable.weakSoundness]

/--
If we know constraints and _some_ of the guarantees unconditionally, we can remove them from the per-row assumptions.

This lemma is tailored to VM-like channels where there remains a single channel that we need to
prove guarantees for.
-/
lemma requirements_of_partial_guarantees_of_constraints {witness : TableWitness F}
  {finished : List (RawChannel F)} {unfinished : RawChannel F} :
  witness.Constraints →
  witness.channelsWithGuarantees ⊆ unfinished :: finished →
  (∀ channel ∈ finished, witness.ChannelGuarantees channel) →
    ∀ row ∈ witness.table,
      witness.abstract.operations.ChannelGuarantees unfinished (witness.environment row) →
      witness.abstract.operations.ChannelRequirements unfinished (witness.environment row) := by
  intro constraints subset finished_grts row h_row channel_grts
  replace finished_grts channel hc := finished_grts channel hc row h_row
  set env := witness.environment row
  suffices witness.abstract.operations.FullRequirements env by
    simp only [circuit_norm] at this ⊢
    intro i hi _
    exact this i hi
  suffices witness.abstract.operations.FullGuarantees env from
    witness.abstract.weakSoundness (constraints row h_row) this |>.right
  simp only [AbstractTable.guarantees_iff, AbstractTable.rowOperations]
  rw [FormalCircuitWithInteractions.guarantees_iff']
  intro channel channel_mem
  show witness.abstract.rowOperations.ChannelGuarantees channel env
  rw [← AbstractTable.channelGuarantees_iff]
  replace channel_mem := subset channel_mem
  simp at channel_mem
  rcases channel_mem with rfl | channel_mem
  · exact channel_grts
  · exact finished_grts _ channel_mem
end TableWitness

variable {PublicIO : TypeMap} [ProvableType PublicIO]

/-- More minimal and general version of EnsembleWitness -/
structure TablesWitness (F : Type) [Field F] [DecidableEq F] where
  tables : List (TableWitness F)
  data : ProverData F
  same_data : ∀ table ∈ tables, table.data = data

namespace TablesWitness
def cons (table : TableWitness F) (witness : TablesWitness F) (same_data : table.data = witness.data) : TablesWitness F where
  tables := table :: witness.tables
  data := witness.data
  same_data := by
    simp [same_data]
    apply witness.same_data

@[circuit_norm] lemma cons_tables {table : TableWitness F} {witness : TablesWitness F} (same_data : table.data = witness.data) :
  (cons table witness same_data).tables = table :: witness.tables := rfl

@[circuit_norm] lemma cons_data {table : TableWitness F} {witness : TablesWitness F} (same_data : table.data = witness.data) :
  (cons table witness same_data).data = witness.data := rfl

def induct {motive : TablesWitness F → Sort*}
  (nil : ∀ data, motive ⟨ [], data, by simp ⟩)
  (cons : ∀ table witness same_data, motive witness → motive (cons table witness same_data))
    (table : TablesWitness F) : motive table := by
  rcases table with ⟨ tables, data, same_data ⟩
  induction tables with
  | nil => exact nil data
  | cons table tables ih =>
    have same_data' : ∀ table ∈ tables, table.data = data := by
      intro table h_table
      apply same_data
      simp [h_table]
    let witness : TablesWitness F := ⟨ tables, data, same_data' ⟩
    have same_data_table : table.data = witness.data := by
      simp [witness, same_data]
    apply cons table witness same_data_table
    exact ih same_data'

def append (witness1 witness2 : TablesWitness F) (same_data : witness1.data = witness2.data) : TablesWitness F where
  tables := witness1.tables ++ witness2.tables
  data := witness1.data
  same_data := by
    simp [or_imp, forall_and]
    constructor
    · apply witness1.same_data
    rw [same_data]
    apply witness2.same_data

@[circuit_norm] lemma append_tables {witness1 witness2 : TablesWitness F} (same_data : witness1.data = witness2.data) :
  (append witness1 witness2 same_data).tables = witness1.tables ++ witness2.tables := rfl

@[circuit_norm] lemma append_data {witness1 witness2 : TablesWitness F} (same_data : witness1.data = witness2.data) :
  (append witness1 witness2 same_data).data = witness1.data := rfl

@[circuit_norm] lemma cons_append {table : TableWitness F} {witness1 witness2 : TablesWitness F}
  (same_data1 : table.data = witness1.data) (same_data2 : witness1.data = witness2.data) :
  (cons table witness1 same_data1).append witness2 same_data2 =
    cons table (append witness1 witness2 same_data2) same_data1 := rfl

@[circuit_norm]
abbrev abstracts (witness : TablesWitness F) : List (AbstractTable F) :=
  witness.tables.map (·.abstract)

instance : Coe (TablesWitness F) (List (TableWitness F)) where
  coe witness := witness.tables

abbrev Constraints (witness : TablesWitness F) : Prop :=
  ∀ table ∈ witness.tables, table.Constraints

noncomputable abbrev interactionsWith (witness : TablesWitness F) (channel : RawChannel F) : List (Interaction F) :=
  witness.tables.flatMap (·.interactionsWith channel)

@[circuit_norm] lemma interactionsWith_cons {table : TableWitness F} {witness : TablesWitness F}
  (same_data : table.data = witness.data) {channel : RawChannel F} :
  interactionsWith (cons table witness same_data) channel =
    table.interactionsWith channel ++ interactionsWith witness channel := by
  simp [interactionsWith, TableWitness.interactionsWith, circuit_norm]

@[circuit_norm] lemma interactionsWith_append {witness1 witness2 : TablesWitness F}
  (same_data : witness1.data = witness2.data) {channel : RawChannel F} :
  interactionsWith (append witness1 witness2 same_data) channel =
    interactionsWith witness1 channel ++ interactionsWith witness2 channel := by
  simp [interactionsWith, TableWitness.interactionsWith, circuit_norm]
end TablesWitness

def balanceOf (interactions : List (Interaction F)) (msg : Array F) : F :=
  interactions.filter (·.msg = msg) |>.map (·.mult) |>.sum

lemma balanceOf_append {as bs : List (Interaction F)} {msg : Array F} :
    balanceOf (as ++ bs) msg = balanceOf as msg + balanceOf bs msg := by
  simp [balanceOf, List.filter_append, List.map_append, List.sum_append]

/-- Interaction balance: for any message, the sum of multiplicities is 0.
  Also requires that the total interaction count does not overflow. -/
def BalancedInteractions (interactions : List (Interaction F)) : Prop :=
  (interactions.length < ringChar F ∨ ringChar F = 0) ∧
  ∀ msg : Array F, balanceOf interactions msg = 0

lemma balanceOf_perm {as bs : List (Interaction F)} {msg : Array F} :
    List.Perm as bs → balanceOf as msg = balanceOf bs msg := by
  intro perm
  apply List.Perm.sum_eq
  exact perm.filter (·.msg = msg) |>.map (·.mult)

lemma balancedInteractions_of_perm {as bs : List (Interaction F)} :
   BalancedInteractions as → List.Perm as bs → BalancedInteractions bs := by
  rintro ⟨ lt_ringChar, balance ⟩ perm
  constructor
  · simp_all [perm.length_eq]
  intro msg
  rw [← balanceOf_perm perm, balance]

lemma msgInteractions_lt_ringChar {ins : List (Interaction F)} {msg : Array F} :
    BalancedInteractions ins → ins.countP (·.msg = msg) < ringChar F ∨ ringChar F = 0 := by
  intro ⟨ lt_ringChar, _ ⟩
  grw [List.countP_le_length]
  exact lt_ringChar

structure Ensemble (F : Type) [Field F] [DecidableEq F] (PublicIO : TypeMap) [ProvableType PublicIO] where
  tables : List (AbstractTable F)
  channels : List (RawChannel F)
  verifier : FormalCircuitWithInteractions F PublicIO unit := .empty F PublicIO
  verifier_length_zero : ∀ pi, verifier.localLength pi = 0 := by
    simp only [FormalCircuitWithInteractions.empty, circuit_norm]
  Spec : PublicIO F → Prop

lemma Ensemble.size_verifier {ens : Ensemble F PublicIO} :
    ens.verifier.size = size PublicIO := by
  simp [FormalCircuitWithInteractions.size_eq, ens.verifier_length_zero]

structure EnsembleWitness (ens : Ensemble F PublicIO) where
  tables : List (TableWitness F)
  data : ProverData F
  publicInput : PublicIO F
  same_length : ens.tables.length = tables.length
  same_circuits : ∀ i (hi : i < ens.tables.length), ens.tables[i] = tables[i].abstract
  same_data : ∀ table ∈ tables, table.data = data

/-- it's convenient to define a `TableWitness` for the verifier, to treat them in a unified way -/
def EnsembleWitness.verifierTable {ens : Ensemble F PublicIO} (witness : EnsembleWitness ens) : TableWitness F where
  abstract := ⟨ ens.verifier ⟩
  width := size PublicIO
  -- it's important that this has one row, which contains the input,
  -- since we want to "run" the verifier once to produce interactions,
  -- and so that constraints etc are actually enforced
  table := [witness.publicInput |> toElements |>.toArray]
  data := witness.data
  uniform_width := by simp

def Ensemble.verifierTable (ens : Ensemble F PublicIO) : AbstractTable F :=
  ⟨ ens.verifier ⟩

def Ensemble.allTables (ens : Ensemble F PublicIO) : List (AbstractTable F) :=
  ens.verifierTable :: ens.tables

-- def emptyEnvironment (F : Type) [Field F] [DecidableEq F] (data : ProverData F) : Environment F :=
--   { get _ := 0, data, interactions := [] }

namespace EnsembleWitness
variable {ens : Ensemble F PublicIO}

def allTables (witness : EnsembleWitness ens) : List (TableWitness F) :=
  witness.verifierTable :: witness.tables

abbrev allTablesWitness (witness : EnsembleWitness ens) : TablesWitness F where
  tables := witness.allTables
  data := witness.data
  same_data := by
    simp [allTables, verifierTable]
    apply witness.same_data

@[circuit_norm] lemma allTablesWitness_tables (witness : EnsembleWitness ens) :
  witness.allTablesWitness.tables = witness.allTables := rfl
@[circuit_norm] lemma allTablesWitness_data (witness : EnsembleWitness ens) :
  witness.allTablesWitness.data = witness.data := rfl

instance : CoeOut (EnsembleWitness ens) (TablesWitness F) where
  coe witness := witness.allTablesWitness

lemma mem_allTables_of_mem_tables (witness : EnsembleWitness ens) {table : TableWitness F} :
    table ∈ witness.tables → table ∈ witness.allTables := by
  simp_all [allTables]

lemma mem_allTables_verifierTable (witness : EnsembleWitness ens) :
    witness.verifierTable ∈ witness.allTables := by
  simp [allTables]

lemma forall_mem_allTables_iff (witness : EnsembleWitness ens)
  (motive : TableWitness F → Prop) :
    (∀ table ∈ witness.allTables, motive table) ↔
    motive witness.verifierTable ∧ (∀ table ∈ witness.tables, motive table) := by
  simp [allTables]

@[circuit_norm]
lemma verifierTable_abstract_eq (witness : EnsembleWitness ens) :
  witness.verifierTable.abstract = ens.verifierTable := rfl

@[circuit_norm]
lemma tables_map_abstract_eq (witness : EnsembleWitness ens) :
    witness.tables.map (·.abstract) = ens.tables := by
  apply List.ext_getElem
  · simp [witness.same_length]
  intro i hi hi'
  simp [witness.same_circuits i hi']

@[circuit_norm]
lemma allTables_map_abstract_eq (witness : EnsembleWitness ens) :
    witness.allTables.map (·.abstract) = ens.allTables := by
  simp only [circuit_norm, allTables, Ensemble.allTables]

lemma mem_tables_abstract_of_mem_tables {witness : EnsembleWitness ens} {table : TableWitness F} :
    table ∈ witness.tables → table.abstract ∈ ens.tables := by
  rw [← witness.tables_map_abstract_eq]
  grind

lemma mem_allTables_abstract_of_mem_allTables {witness : EnsembleWitness ens} {table : TableWitness F} :
    table ∈ witness.allTables → table.abstract ∈ ens.allTables := by
  rw [← witness.allTables_map_abstract_eq]
  grind

def Constraints {ens : Ensemble F PublicIO} (witness : EnsembleWitness ens) : Prop :=
  ∀ table ∈ witness.allTables, table.Constraints

def interactions {ens : Ensemble F PublicIO} (witness : EnsembleWitness ens) : List (Interaction F) :=
  (witness.allTables).flatMap (fun table => table.interactions)

noncomputable def interactionsWith {ens : Ensemble F PublicIO} (witness : EnsembleWitness ens)
    (channel : RawChannel F) : List (Interaction F) :=
  witness.allTables.flatMap (·.interactionsWith channel)

@[circuit_norm] lemma allTablesWitness_constraints {ens : Ensemble F PublicIO} (witness : EnsembleWitness ens) :
    witness.allTablesWitness.Constraints ↔ witness.Constraints := by
  simp only [TablesWitness.Constraints, Constraints]

@[circuit_norm] lemma interactionsWith_allTablesWitness {ens : Ensemble F PublicIO}
  (witness : EnsembleWitness ens) (channel : RawChannel F) :
    witness.allTablesWitness.interactionsWith channel = witness.interactionsWith channel := rfl
end EnsembleWitness

namespace Ensemble
variable {ens : Ensemble F PublicIO}

@[circuit_norm] lemma verifierTable_circuit : ens.verifierTable.circuit = ens.verifier := rfl
@[circuit_norm] lemma verifierTable_input : ens.verifierTable.Input = PublicIO := rfl

lemma mem_same_prover_data (witness : EnsembleWitness ens) :
    ∀ table ∈ witness.allTables, table.data = witness.data := by
  rw [witness.forall_mem_allTables_iff]
  simp only [EnsembleWitness.verifierTable, true_and]
  exact witness.same_data

lemma verifierTable_ext {ens1 ens2 : Ensemble F PublicIO} {witness1 : EnsembleWitness ens1} {witness2 : EnsembleWitness ens2} :
    ens1.verifier = ens2.verifier →
    witness1.publicInput = witness2.publicInput →
    witness1.data = witness2.data →
      witness1.verifierTable = witness2.verifierTable := by
  rintro h_circuit h_input h_data
  simp [EnsembleWitness.verifierTable, h_circuit, h_input, h_data]

@[circuit_norm]
abbrev verifierOperations (ens : Ensemble F PublicIO) : Operations F :=
  (ens.verifier.main (varFromOffset PublicIO 0)).operations (size PublicIO)

def VerifierConstraints (ens : Ensemble F PublicIO) (publicInput : PublicIO F) (data : ProverData F) : Prop :=
  ens.verifierOperations.ConstraintsHold (.fromInput publicInput data)

def VerifierGuarantees (ens : Ensemble F PublicIO) (publicInput : PublicIO F) (data : ProverData F) : Prop :=
  ens.verifierOperations.FullGuarantees (.fromInput publicInput data)

def VerifierChannelGuarantees (ens : Ensemble F PublicIO) (channel : RawChannel F) (publicInput : PublicIO F) (data : ProverData F) : Prop :=
  ens.verifierOperations.ChannelGuarantees channel (.fromInput publicInput data)

def VerifierRequirements (ens : Ensemble F PublicIO) (publicInput : PublicIO F) (data : ProverData F) : Prop :=
  ens.verifierOperations.FullRequirements (.fromInput publicInput data)

def VerifierSpec (ens : Ensemble F PublicIO) (publicInput : PublicIO F) (data : ProverData F) : Prop :=
  ens.verifier.Spec publicInput () (.fromInput publicInput data)

lemma verifierTable_constraints :
  ens.verifierTable.operations.constraints = ens.verifierOperations.constraints := by
  rw [AbstractTable.constraints_eq]
  simp only [circuit_norm]

lemma verifierTable_lookups :
  ens.verifierTable.operations.lookups = ens.verifierOperations.lookups := by
  rw [AbstractTable.lookups_eq]
  simp only [circuit_norm]

lemma verifierTable_interactions :
  ens.verifierTable.operations.interactions = ens.verifierOperations.interactions := by
  rw [AbstractTable.interactions_eq]
  simp only [circuit_norm]

lemma verifierTable_interactionsWith {channel : RawChannel F} :
  ens.verifierTable.operations.interactionsWith channel =
    ens.verifierOperations.interactionsWith channel := by
  rw [AbstractTable.interactionsWith_eq]
  simp only [circuit_norm]
end Ensemble

namespace EnsembleWitness
variable {ens : Ensemble F PublicIO}

lemma mem_interactionsWith {witness : EnsembleWitness ens}
  {channel : RawChannel F} {i : Interaction F} :
    i ∈ witness.interactionsWith channel ↔
    ∃ table ∈ witness.allTables, i ∈ table.interactionsWith channel := by
  simp only [interactionsWith, List.mem_flatMap]

lemma channel_eq_of_mem_interactionsWith {witness : EnsembleWitness ens}
  {channel : RawChannel F} {i : Interaction F} :
    i ∈ witness.interactionsWith channel → i.channel = channel := by
  rw [mem_interactionsWith]
  intro h_mem
  rcases h_mem with ⟨ table, h_table, h_mem_table ⟩
  apply table.channel_eq_of_mem_interactionsWith h_mem_table

@[circuit_norm]
lemma verifierTable_forall {witness : EnsembleWitness ens}
      {motive : Array F → Prop} :
    (∀ row ∈ witness.verifierTable.table, motive row) ↔ motive (toElements witness.publicInput).toArray := by
  simp [EnsembleWitness.verifierTable]

@[circuit_norm]
lemma verifierTable_flatMap {witness : EnsembleWitness ens}
      {α : Type*} {f : Array F → List α} :
    witness.verifierTable.table.flatMap f = f (toElements witness.publicInput).toArray := by
  simp [EnsembleWitness.verifierTable]

@[circuit_norm]
lemma verifierTable_environment {witness : EnsembleWitness ens} {publicInput : PublicIO F} :
    witness.verifierTable.environment (toElements publicInput).toArray =
      Environment.fromInput publicInput witness.data := rfl

lemma verifierConstraints_iff_verifierTable_constraints {witness : EnsembleWitness ens} :
  ens.VerifierConstraints witness.publicInput witness.data ↔
    witness.verifierTable.Constraints := by
  simp only [Ensemble.VerifierConstraints, TableWitness.Constraints]
  simp only [circuit_norm, Ensemble.verifierTable_constraints, Ensemble.verifierTable_lookups]

lemma verifierConstraints_of_constraints {ens : Ensemble F PublicIO} {witness : EnsembleWitness ens} :
  witness.Constraints →
    ens.VerifierConstraints witness.publicInput witness.data := by
  rw [verifierConstraints_iff_verifierTable_constraints, Constraints, EnsembleWitness.forall_mem_allTables_iff]
  simp_all

lemma interactionsWith_of_verifier_empty {ens : Ensemble F PublicIO} {witness : EnsembleWitness ens} {channel : RawChannel F}
  (h_verifier_empty : ens.verifier = .empty F PublicIO) :
    witness.interactionsWith channel = witness.tables.flatMap (·.interactionsWith channel) := by
  simp [EnsembleWitness.interactionsWith, EnsembleWitness.allTables, TableWitness.interactionsWith,
    Ensemble.verifierTable_interactionsWith, circuit_norm, h_verifier_empty]

lemma verifierTable_constraints_of_verifier_empty {ens : Ensemble F PublicIO} {witness : EnsembleWitness ens}
  (h_verifier_empty : ens.verifier = .empty F PublicIO) :
    witness.verifierTable.Constraints := by
  rw [← verifierConstraints_iff_verifierTable_constraints]
  simp only [Ensemble.VerifierConstraints, circuit_norm, h_verifier_empty]

/-- The ensemble interactions with a particular channel are balanced. -/
abbrev BalancedChannel {ens : Ensemble F PublicIO} (witness : EnsembleWitness ens)
    (channel : RawChannel F) : Prop :=
  BalancedInteractions (witness.allTablesWitness.interactionsWith channel)

/-- All ensemble interactions with all ensemble channels are balanced. -/
def BalancedChannels {ens : Ensemble F PublicIO} (witness : EnsembleWitness ens) : Prop :=
  ∀ channel ∈ ens.channels, BalancedChannel witness channel
end EnsembleWitness

namespace Ensemble
/--
Soundness for an ensemble states that if
- constraints hold on all tables and
- and interactions sum to zero
- and constraints hold on the verifier circuit, when given the public inputs (as constants)
then the spec holds
-/
def Soundness (F : Type) [Field F] [DecidableEq F] (ens : Ensemble F PublicIO) : Prop :=
  ∀ (witness : EnsembleWitness ens),
    witness.BalancedChannels →
    witness.Constraints →
    ens.Spec witness.publicInput

/--
Completeness for an ensemble states that for any public input satisfying the spec,
the verifier accepts and there exists a witness such that constraints hold and the channels are balanced
-/
def Completeness (ens : Ensemble F PublicIO) : Prop :=
  -- TODO data should not be here!!
  ∀ publicInput data,
    ens.Spec publicInput →
    ens.VerifierConstraints publicInput data ∧
    ∃ (witness : EnsembleWitness ens),
      witness.data = data ∧ witness.publicInput = publicInput ∧
      witness.Constraints ∧ witness.BalancedChannels
end Ensemble

-- infrastructure for iteratively adding tables to an ensemble such that we can always fill in
-- the next table's guarantees

/--
we call a channel "consistent" if balancedness + requirements on all interacions
imply guarantees on all interactions.

this can be proved for individual channels without reference to any constraints,
essentially just means that reqs and grts are reasonably related.
-/
class RawChannel.Consistent (channel : RawChannel F) : Prop where
  consistent : ∀ (interactions : List (Interaction F)) (data : ProverData F),
    BalancedInteractions interactions →
    (∀ i ∈ interactions, i.channel = channel ∧ i.Requirements data) →
    (∀ i ∈ interactions, i.Guarantees data)

/--
Relaxed version of BalancedChannel that works with ensembles that aren't fully specified yet,
where we assume our interactions are a subset of some larger list which is balanced.

designed to be used for proving soundness by adding one table after another.
-/
def PartialBalancedChannel (tables : TablesWitness F) (channel : RawChannel F) : Prop :=
  -- `extraInteractions` represents the unknown interactions from tables added later
  ∃ extraInteractions : List (Interaction F),
    -- the total of known + unknown interactions is balanced for each "finished" channel
    BalancedInteractions (tables.interactionsWith channel ++ extraInteractions) ∧
    -- the extra interactions are with the same channel.
    (∀ i ∈ extraInteractions, i.channel = channel) ∧
    -- additionally, we _assume_ that either the requirements on future interactions hold unconditionally,
    -- or that known interactions do not assume guarantees on the same channel.
    -- this restricts the order in which tables can be added. essentially, it requires that the `extraTables`
    -- that create the `extraInteractions` satisfy `OrderedChannelLt channel tables extraTables` (see below);
    -- and it's the missing piece when reasoning about requirements and guarantees on the full list of balanced interactions.
    (channel ∉ tables.tables.flatMap (·.channelsWithGuarantees) ∨ ∀ i ∈ extraInteractions, i.Requirements tables.data)

/-- Partial balance is trivially weaker than balance -/
lemma partialBalancedChannel_of_balancedInteractions {tables : TablesWitness F} {channel : RawChannel F} :
    BalancedInteractions (tables.interactionsWith channel) → PartialBalancedChannel tables channel := by
  intro balanced
  use []
  simp [balanced]

@[circuit_norm]
lemma List.flatMap_subset_iff {α β : Type*} {f : α → List β} {l₁ : List α} {l₂ : List β} :
    l₁.flatMap f ⊆ l₂ ↔ ∀ a ∈ l₁, f a ⊆ l₂ := by
  grind

-- TODO deduplicate and add to Basic
attribute [circuit_norm] forall_eq_or_imp List.mem_flatMap List.mem_map exists_exists_and_eq_and
  not_exists not_and List.Subset.refl List.subset_append_of_subset_left List.subset_append_of_subset_right
  List.flatMap_append List.mem_append not_or not_exists not_and not_false_eq_true
  List.flatMap_cons List.append_subset

/--
A channel is "ordered" in a list of tables if all the tables that add requirements
come before all the tables that add guarantees for the channel.

Note that the order is reversed compared to the intended hierarchy, this is just because it's the
more natural direction for doing List.cons induction, so we think of a cons'd element as coming
after the rest of the list.
-/
def OrderedChannel (channel : RawChannel F) (tables : List (AbstractTable F)) : Prop :=
  ∀ i (hi : i < tables.length) j (hj : j < tables.length),
    channel ∈ tables[i].circuit.channelsWithGuarantees →
    channel ∈ tables[j].circuit.channelsWithRequirements →
      i < j

@[circuit_norm]
lemma orderedChannel_nil (channel : RawChannel F) : OrderedChannel channel [] := by
  simp [OrderedChannel]

@[circuit_norm]
abbrev OrderedChannelRefl (channel : RawChannel F) (table : AbstractTable F) : Prop :=
  channel ∉ table.circuit.channelsWithGuarantees ∨ channel ∉ table.circuit.channelsWithRequirements

abbrev OrderedChannelLt (channel : RawChannel F) (tables₁ tables₂ : List (AbstractTable F)) : Prop :=
  channel ∉ tables₁.flatMap (·.circuit.channelsWithGuarantees) ∨ channel ∉ tables₂.flatMap (·.circuit.channelsWithRequirements)

@[circuit_norm]
lemma orderedChannelLt_nil_right (channel : RawChannel F) (tables : List (AbstractTable F)) :
    OrderedChannelLt channel tables [] := by simp [OrderedChannelLt]

@[circuit_norm]
lemma orderedChannelLt_nil_left (channel : RawChannel F) (tables : List (AbstractTable F)) :
    OrderedChannelLt channel [] tables := by simp [OrderedChannelLt]

@[circuit_norm]
lemma orderedChannelLt_cons_right (channel : RawChannel F) {table : AbstractTable F} {ts ss : List (AbstractTable F)} :
  OrderedChannelLt channel ss (table :: ts) ↔
    (channel ∉ ss.flatMap (·.circuit.channelsWithGuarantees) ∨ channel ∉ table.circuit.channelsWithRequirements) ∧
    OrderedChannelLt channel ss ts := by
  simp [OrderedChannelLt, circuit_norm]
  tauto

@[circuit_norm]
lemma orderedChannelLt_append_left {channel : RawChannel F} {ts₁ ts₂ ss : List (AbstractTable F)} :
  OrderedChannelLt channel (ts₁ ++ ts₂) ss ↔
    OrderedChannelLt channel ts₁ ss ∧ OrderedChannelLt channel ts₂ ss := by
  simp only [OrderedChannelLt, circuit_norm]
  tauto

@[circuit_norm]
lemma orderedChannel_append_right {channel : RawChannel F} {ts ss₁ ss₂ : List (AbstractTable F)} :
  OrderedChannelLt channel ts (ss₁ ++ ss₂) ↔
    OrderedChannelLt channel ts ss₁ ∧ OrderedChannelLt channel ts ss₂ := by
  simp only [OrderedChannelLt, circuit_norm]
  tauto

@[circuit_norm]
lemma orderedChannel_cons (table : AbstractTable F) (tables : List (AbstractTable F)) (channel : RawChannel F) :
  OrderedChannel channel (table :: tables) ↔
  OrderedChannelRefl channel table ∧ OrderedChannel channel tables ∧ OrderedChannelLt channel tables [table] := by
  simp only [circuit_norm, OrderedChannel, OrderedChannelRefl, List.length_cons]
  -- Intuition: The `i < j` conclusion of `OrderedChannel` falsifies the hypotheses if `j = 0`,
  -- so apart from the "induction hypothesis" where `i, j > 0`, we get two distinct statements by specializing to `i = 0` and `i > 0` respectively
  simp [Nat.forall_lt_succ_left', List.getElem_cons_zero, List.getElem_cons_succ]
  rw [forall₂_and, List.forall_mem_iff_getElem, or_iff_not_imp_left, or_iff_not_imp_left]
  push_neg
  simp only [exists_imp]
  tauto

lemma orderedChannel_singleton_iff (table : AbstractTable F) (channel : RawChannel F) :
    OrderedChannel channel [table] ↔ OrderedChannelRefl channel table := by
  simp [circuit_norm]

/-- Alternative, and sometimes more convenient, formulation of `OrderedChannel` -/
lemma orderedChannel_iff (tables : List (AbstractTable F)) (channel : RawChannel F) :
  OrderedChannel channel tables ↔
    (∀ t ∈ tables, OrderedChannelRefl channel t) ∧
    ∀ ts ss, tables = ts ++ ss → OrderedChannelLt channel ss ts := by
  simp [OrderedChannel, OrderedChannelLt, OrderedChannelRefl]
  constructor
  · intro ordered_channel
    constructor
    · simp only [List.forall_mem_iff_getElem]
      intro i hi
      specialize ordered_channel i hi i hi
      simp at ordered_channel
      tauto
    intro ts ss h_append
    subst h_append
    simp only [List.length_append] at ordered_channel
    simp only [List.forall_mem_iff_getElem, or_iff_not_imp_left]
    push_neg
    rintro ⟨ i, hi, grts ⟩ j hj reqs
    specialize ordered_channel (ts.length + i) (by linarith) j (by linarith)
    rw [List.getElem_append_right (by omega), List.getElem_append_left (by omega)] at ordered_channel
    have : ¬(ts.length + i < j) := by omega
    apply this
    apply ordered_channel ?_ reqs
    have : ts.length + i - ts.length = i := by simp
    convert grts
  intro ordered_channel' i hi j hj
  simp only [List.forall_mem_iff_getElem] at ordered_channel'
  suffices j = i ∨ j < i →
    channel ∉ tables[i].circuit.channelsWithGuarantees ∨
    channel ∉ tables[j].circuit.channelsWithRequirements by grind
  rintro h
  rcases h with rfl | j_lt_i
  · exact ordered_channel'.left j hi
  have j_succ_lt : j + 1 < tables.length := by linarith
  replace ordered_channel' := ordered_channel'.right (tables.take (j + 1)) (tables.drop (j + 1)) (by simp)
  simp at ordered_channel'
  rcases ordered_channel' with no_grts | no_reqs
  · left
    specialize no_grts (i - (j + 1)) (by omega)
    rw [List.getElem_drop] at no_grts
    have : i = j + 1 + (i - (j + 1)) := by omega
    convert no_grts
  · right
    specialize no_reqs j (by omega) hj
    rw [List.getElem_take] at no_reqs
    exact no_reqs

/-- "Merge sort" for ordered channels -/
@[circuit_norm]
lemma orderedChannel_append (ts ss : List (AbstractTable F)) (channel : RawChannel F) :
  OrderedChannel channel (ts ++ ss) ↔
    OrderedChannel channel ts ∧ OrderedChannel channel ss ∧ OrderedChannelLt channel ss ts := by
  simp only [orderedChannel_iff]
  constructor
  · grind
  · simp only [List.append_eq_append_iff, ←exists_or]
    grind

/-- A sufficient condition for ordered channel is that there are no requirements added -/
lemma orderedChannel_of_no_requirements {channel : RawChannel F} {tables : List (AbstractTable F)} :
  (∀ table ∈ tables, channel ∉ table.circuit.channelsWithRequirements) →
    OrderedChannel channel tables := by
  intro reqs
  rw [orderedChannel_iff]
  simp_all [OrderedChannelRefl, OrderedChannelLt]

/-- A sufficient condition for ordered channel is that there are no guarantees added -/
lemma orderedChannel_of_no_guarantees {channel : RawChannel F} {tables : List (AbstractTable F)} :
  (∀ table ∈ tables, channel ∉ table.circuit.channelsWithGuarantees) →
    OrderedChannel channel tables := by
  intro grts
  rw [orderedChannel_iff]
  simp_all [OrderedChannelRefl, OrderedChannelLt]

/-- A sufficient condition for ordered channel lt is that there are no requirements added in the second list -/
lemma orderedChannelLt_of_no_requirements {channel : RawChannel F} {ts ss : List (AbstractTable F)} :
  (∀ table ∈ ts, channel ∉ table.circuit.channelsWithRequirements) →
    OrderedChannelLt channel ss ts := by
  intro no_reqs
  simp_all [OrderedChannelLt]

/-- A sufficient condition for ordered channel lt is that there are no guarantees added in the first list -/
lemma orderedChannelLt_of_no_guarantees {channel : RawChannel F} {ts ss : List (AbstractTable F)} :
  (∀ table ∈ ss, channel ∉ table.circuit.channelsWithGuarantees) →
    OrderedChannelLt channel ss ts := by
  intro no_grts
  simp_all [OrderedChannelLt]

/--
For ordered channels, we can always instantiate partial balance at an initial sublist.
-/
theorem partialBalancedChannel_of_cons_of_orderedChannelLt
  {table : TableWitness F} {tables : TablesWitness F} (same_data : table.data = tables.data)
  {channel : RawChannel F} :
  PartialBalancedChannel (.cons table tables same_data) channel →
  OrderedChannelLt channel tables.abstracts [table.abstract] →
    PartialBalancedChannel tables channel := by
  rintro ⟨ extraInteractions, balanced, same_channel, extra_reqs_or_no_grts ⟩ not_in_reqs_or
  use table.interactionsWith channel ++ extraInteractions
  simp only [circuit_norm] at *
  simp [or_imp] at ⊢ not_in_reqs_or extra_reqs_or_no_grts
  constructor
  · apply balancedInteractions_of_perm balanced
    grw [List.perm_append_comm_assoc]
  constructor
  · intro a
    use TableWitness.channel_eq_of_mem_interactionsWith
    exact same_channel a
  rw [forall_and]
  rcases not_in_reqs_or with channel_not_in_grts | channel_not_in_reqs
  · simp_all
  rcases extra_reqs_or_no_grts with no_grts | extra_reqs
  · simp_all
  · right
    have channel_reqs := table.requirements_of_not_mem channel_not_in_reqs
    rw [TableWitness.channelRequirements_iff_forall, same_data] at channel_reqs
    exact ⟨ channel_reqs, extra_reqs ⟩

/--
For ordered channels, we can always instantiate partial balance at an initial sublist.
-/
lemma partialBalancedChannel_of_cons_of_orderedChannel
  {table : TableWitness F} {tables : TablesWitness F} (same_data : table.data = tables.data)
  {channel : RawChannel F} :
  OrderedChannel channel (table.abstract :: tables.abstracts) →
  PartialBalancedChannel (tables.cons table same_data) channel →
    PartialBalancedChannel tables channel := by
  intro ordered_channel partial_balance
  apply partialBalancedChannel_of_cons_of_orderedChannelLt same_data partial_balance
  simp_all [circuit_norm]

/--
The significance of `OrderedChannel` is that it lets us prove soundness
on a list of tables by induction. This lemma captures the main step.
-/
lemma guarantees_of_requirements_cons
  -- given a list of tables, and one additional table
  {table : TableWitness F} {tables : TablesWitness F} (same_data : table.data = tables.data)
  -- and a channel that is consistent, ordered on the new table, and partially balanced on the combined tables
  {channel : RawChannel F} [channel.Consistent] :
  OrderedChannelRefl channel table.abstract →
  PartialBalancedChannel (tables.cons table same_data) channel →
  -- the channel requirements on the old tables imply guarantees on the new table
  (∀ table ∈ tables.tables, table.ChannelRequirements channel) →
    table.ChannelGuarantees channel := by
  rintro ordered_channel partial_balance ih
  /-
  thanks to ordered channel, we know that channel cannot add _both_ grts and reqs for the new table.
  1) if the channel does not add grts, we're done as the grts are trivially satisifed.
  2) if the channel does not add reqs, we can prove that _all_ reqs of that channel are satisfied.
      using consistent channels, we conclude the channel's guarantees.
  -/
  simp only [circuit_norm] at ordered_channel
  rcases ordered_channel with grts | reqs
  · exact table.guarantees_of_not_mem grts
  replace reqs := table.requirements_of_not_mem reqs
  -- there's a special case to discard where the guarantees are trivially satisfied
  rcases partial_balance with ⟨ extraInteractions, balanced, same_channel, grts | extra_reqs ⟩
  · simp only [circuit_norm] at grts
    exact table.guarantees_of_not_mem grts.left
  -- now, to prove this table's channel guarantees, we show guarantees on _all_ channel interactions (that we know are balanced)
  set channelInteractions := (tables.cons table same_data).interactionsWith channel ++ extraInteractions
  have subset_channelInteractions : table.interactionsWith channel ⊆ channelInteractions := by
    simp only [channelInteractions, circuit_norm]
  suffices all_grts : ∀ i ∈ channelInteractions, i.Guarantees tables.data by
    rw [TableWitness.channelGuarantees_iff_forall, same_data]
    intro i hi
    exact all_grts i (subset_channelInteractions hi)
  -- this works since we can prove all channel _requirements_
  -- relies on `ordered_channels` and `partial_balance` (the extra interactions assumption)
  have all_reqs : ∀ i ∈ channelInteractions, i.channel = channel ∧ i.Requirements tables.data := by
    simp only [channelInteractions, circuit_norm]
    intro i h_mem
    rcases h_mem with h_mem_table | h_mem_old | h_mem_extra
    -- for the new table, we can just use the requirements assumption
    · rw [TableWitness.channelRequirements_iff_forall, same_data] at reqs
      use table.channel_eq_of_mem_interactionsWith h_mem_table
      exact reqs _ h_mem_table
    · obtain ⟨ table', h_table', i_mem_table ⟩ := h_mem_old
      simp only [TableWitness.channelRequirements_iff_forall] at ih
      specialize ih table' h_table'
      simp only [tables.same_data _ h_table'] at ih
      use table'.channel_eq_of_mem_interactionsWith i_mem_table
      exact ih i i_mem_table
    · exact ⟨ same_channel i h_mem_extra, extra_reqs i h_mem_extra ⟩
  -- consistent channels goes from requirements to guarantees
  -- uses `consistent_channels` and `partial_balance`
  apply ‹channel.Consistent›.consistent channelInteractions tables.data balanced all_reqs

/--
Partial balance can be specialized to a sublist (= part of a permutation),
as long as none of the extra tables add requirements.
-/
lemma partialBalancedChannel_of_sublist {subtables tables : TablesWitness F} {channel : RawChannel F} :
  PartialBalancedChannel tables channel →
  (∃ otherTables, tables.tables.Perm (subtables.tables ++ otherTables) ∧
    ∀ table ∈ otherTables, channel ∉ table.channelsWithRequirements) →
    PartialBalancedChannel subtables channel := by
  rintro ⟨ extraInteractions, balanced, same_channel, no_grts_or_extra_reqs ⟩ subset_tables
  obtain ⟨ otherTables, perm, otherReqs ⟩ := subset_tables
  by_cases subtables_empty : subtables.tables = []
  · simp [subtables_empty, circuit_norm, PartialBalancedChannel, TablesWitness.interactionsWith]
    use []
    simp [BalancedInteractions, balanceOf]
    omega
  have subtables_subset : subtables.tables ⊆ tables.tables := by
    have p := perm.symm.subset
    simp_all
  have subtables_data : subtables.data = tables.data := by
    have ⟨ one_subtable, h_one_subtable ⟩ : ∃ table, table ∈ subtables.tables := by
      apply List.exists_mem_of_ne_nil
      simp [subtables_empty]
    rw [← subtables.same_data _ h_one_subtable,
      tables.same_data _ (subtables_subset h_one_subtable)]
  use otherTables.flatMap (·.interactionsWith channel) ++ extraInteractions
  simp_all only
  constructor; swap
  -- TODO this half is surprisingly long/annoying, maybe missing helper lemmas
  · simp [circuit_norm, or_imp]
    constructor
    · intro i
      use fun _ _ => TableWitness.channel_eq_of_mem_interactionsWith
      exact same_channel i
    rcases no_grts_or_extra_reqs with no_grts | extra_reqs
    · simp only [List.mem_flatMap, not_exists, not_and] at no_grts
      left
      intro t ht
      exact no_grts _ (subtables_subset ht)
    right
    intro i
    constructor; swap
    · exact extra_reqs i
    intro t ht
    revert i
    have ht' : t ∈ tables.tables := by
      apply perm.symm.subset
      simp [ht]
    rw [← tables.same_data _ ht', ← TableWitness.channelRequirements_iff_forall]
    apply TableWitness.requirements_of_not_mem
    exact otherReqs _ ht
  -- balance
  apply balancedInteractions_of_perm balanced
  simp only [TablesWitness.interactionsWith]
  grw [← List.append_assoc, List.perm_append_right_iff, ← List.flatMap_append, perm.flatMap]
  exact fun _ _ => List.Perm.refl _

/--
The argument of `guarantees_of_requirements_cons`
also works for adding multiple new tables, if we make the assumption a bit stronger:
We can no longer continue to introduce guarantees for the channel.

This is relevant later when we add VM channels on top of an already finished, sound ensemble.
-/
lemma guarantees_of_requirements_append
  -- given two lists of tables
  {ts ss : TablesWitness F} (same_data : ts.data = ss.data)
  -- and a channel that is consistent, _doesn't add requirements_ on the new tables,
  -- and is partially balanced on the combined tables
  {channel : RawChannel F} [channel.Consistent] :
  (∀ table ∈ ts.tables, channel ∉ table.abstract.circuit.channelsWithRequirements) →
  PartialBalancedChannel (ts.append ss same_data) channel →
  -- the channel requirements on the old tables imply guarantees on the new tables
  (∀ table ∈ ss.tables, table.ChannelRequirements channel) →
    ∀ table ∈ ts.tables, table.ChannelGuarantees channel := by
  -- we show that for each (t, ss) pair, the assumptions of `*_cons` hold
  rintro reqs partial_balance ih table h_table
  have same_data' : table.data = ss.data := by
    rw [ts.same_data _ h_table, same_data]
  apply guarantees_of_requirements_cons (tables := ss) same_data' ?_ ?_ ih
  · right; exact reqs _ h_table
  -- get partial balance by sublist/permutation argument
  apply partialBalancedChannel_of_sublist partial_balance
  obtain ⟨ i, hi, h' ⟩ := List.getElem_of_mem h_table
  symm at h'; subst h'
  use ts.tables.eraseIdx i
  constructor; swap
  · intro t' ht'
    apply reqs _ (List.mem_of_mem_eraseIdx ht')
  simp [circuit_norm]
  grw [List.perm_append_comm, List.perm_cons_append_cons _ List.perm_rfl,
    List.perm_append_left_iff, List.perm_comm]
  apply List.getElem_cons_eraseIdx_perm

/-- Helper lemma that uses circuit soundness, to strengthen guarantees to include requirements -/
lemma iff_guarantees_of_constraints {table : TableWitness F} {finished : List (RawChannel F)} :
  table.Constraints →
  table.abstract.circuit.channelsWithGuarantees ⊆ finished →
  ((table.Spec ∧ ∀ channel ∈ finished, table.ChannelGuarantees channel ∧ table.ChannelRequirements channel) ↔
    ∀ channel ∈ finished, table.ChannelGuarantees channel) := by
  intro constraints subset_finished
  constructor; simp_all
  intro grts
  have all_grts : table.Guarantees := by
    rw [TableWitness.guarantees_iff_channelGuarantees]
    intro channel h_channel
    exact grts _ (subset_finished h_channel)
  -- constraints ∧ guarantees → requirements → channelRequirements
  have ⟨ spec, all_reqs ⟩ := table.weakSoundness constraints all_grts
  use spec
  intro channel h_channel
  exact ⟨ grts _ h_channel, table.channelRequirements_of_requirements all_reqs ⟩

/--
`SoundChannels` combines three assumptions on the channels used by a list of tables,
that together are

- sufficient for proving soundness of just these tables
- help with proving soundness of additional tables, by handling the guarantees of finished channels.

Notably, `SoundChannels` can be stated and proved entirely (and easily) from the knowledge of each table's
`channelsWithGuarantees` and `channelsWithRequirements`.

In practice, this property holds on ensembles that only use channels in lookup fashion.

Note: In the presence of "VM-like" channels, where a circuit both pushes and pulls to the same channel,
`SoundChannels` does not hold for _any_ list of channels:
- VM channels don't satisfy `OrderedChannel`, so they disqualify for the `finished` list.
- Consequently, the first property `channelsWithGuarantees ⊆ finished` is violated for VM tables, since
  VM channels do belong to the `channelsWithGuarantees`.
However, in that scenario, it is still useful to establish `SoundChannels` on the subset of non-VM tables.
-/
@[circuit_norm]
def SoundChannels (tables : List (AbstractTable F)) (finished : List (RawChannel F)) : Prop :=
  (∀ table ∈ tables, table.circuit.channelsWithGuarantees ⊆ finished) ∧
  (∀ channel ∈ finished, OrderedChannel channel tables) ∧
  ∀ channel ∈ finished, channel.Consistent

/-- `SoundChannels` lets us prove a soundness theorem. -/
theorem spec_and_guarantees_of_soundChannels {witness : TablesWitness F} {finished : List (RawChannel F)} :
  SoundChannels (witness.tables.map (·.abstract)) finished →
  -- constraints + partial balance
  witness.Constraints →
  (∀ channel ∈ finished, PartialBalancedChannel witness channel) →
    -- implies the spec, and the guarantees and requirements on all finished channels
    ∀ table ∈ witness.tables, table.Spec ∧ ∀ channel ∈ finished,
    table.ChannelGuarantees channel ∧ table.ChannelRequirements channel := by
  -- by induction on the tables
  rintro ⟨ subset_finished, ordered_channels, consistent_channels ⟩ constraints partial_balance
  induction witness using TablesWitness.induct
  · intro _ h_table; nomatch h_table
  -- induction step
  rename_i table tables same_data ih
  -- first, we use the IH
  have partial_balance' c hc := partialBalancedChannel_of_cons_of_orderedChannel
    same_data (ordered_channels c hc) (partial_balance c hc)
  simp only [TablesWitness.Constraints, circuit_norm] at *
  simp only [forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at *
  specialize ih subset_finished.right (fun c hc => (ordered_channels c hc).right.left)
    constraints.right partial_balance'
  constructor; swap
  · exact ih
  -- it's enough to prove guarantees of all channels, since they + constraints imply requirements
  rw [iff_guarantees_of_constraints constraints.left subset_finished.left]
  -- the rest is just applying `guarantees_of_requirements_cons`
  intro channel h_channel
  have : channel.Consistent := consistent_channels _ h_channel
  have orderedChannelRefl : OrderedChannelRefl channel table.abstract := by
    simp only [circuit_norm, ordered_channels channel h_channel]
  apply guarantees_of_requirements_cons same_data
    orderedChannelRefl (partial_balance channel h_channel)
  intro t ht
  exact (ih t ht).right _ h_channel |>.right

/-- `SoundChannels` is strictly increasing: you can make the finished list bigger by any consistent channels -/
lemma soundChannels_of_soundChannels_subset {tables : List (AbstractTable F)} {finished finished' : List (RawChannel F)} :
  SoundChannels tables finished →
  finished ⊆ finished' →
  (∀ channel ∈ finished', channel.Consistent) →
    SoundChannels tables finished' := by
  rintro ⟨ subset_finished, ordered_channels, consistent_channels ⟩ finished'_subset finished'_consistent
  constructor
  · intro table h_table
    specialize subset_finished table h_table
    trans finished <;> assumption
  constructor; swap
  · assumption
  intro channel h_channel
  by_cases h_channel_finished : channel ∈ finished
  · apply ordered_channels channel h_channel_finished
  apply orderedChannel_of_no_guarantees
  intro table h_table mem_grts
  apply h_channel_finished
  exact subset_finished table h_table mem_grts

/-- You can add one channel to the finished list and preserve `SoundChannels` -/
lemma soundChannels_cons_of_soundChannels {tables : List (AbstractTable F)}
  {finished : List (RawChannel F)} {channel : RawChannel F} [channel.Consistent] :
  SoundChannels tables finished →
    SoundChannels tables (channel :: finished) := by
  intro sound_channels
  apply soundChannels_of_soundChannels_subset sound_channels
  · simp
  simp_all [SoundChannels]

namespace EnsembleWitness
abbrev PartialBalancedChannel {ens : Ensemble F PublicIO} (witness : EnsembleWitness ens) (channel : RawChannel F) : Prop :=
  _root_.PartialBalancedChannel witness channel

abbrev PartialBalancedChannels {ens : Ensemble F PublicIO} (finished : List (RawChannel F))
    (witness : EnsembleWitness ens) : Prop :=
  ∀ channel ∈ finished, witness.PartialBalancedChannel channel
end EnsembleWitness

namespace Ensemble
def empty (F : Type) [Field F] [DecidableEq F] (PublicIO : TypeMap) [ProvableType PublicIO] :
  Ensemble F PublicIO where
    tables := []
    channels := []
    Spec _ := True

@[circuit_norm] lemma empty_tables :
  (empty F PublicIO).tables = [] := rfl
@[circuit_norm] lemma empty_channels :
  (empty F PublicIO).channels = [] := rfl
@[circuit_norm] lemma empty_verifier :
  (empty F PublicIO).verifier = .empty F PublicIO := rfl
@[circuit_norm] lemma empty_allTables :
  (empty F PublicIO).allTables = [⟨ .empty F PublicIO ⟩] := rfl

/-- Partial balanced channel is trivially weaker than balanced channel -/
lemma partialBalancedChannel_of_balancedChannel {ens : Ensemble F PublicIO}
    {witness : EnsembleWitness ens} (channel : RawChannel F) :
  witness.BalancedChannel channel →
    witness.PartialBalancedChannel channel := by
  intro balanced
  use []
  simp_all [EnsembleWitness.BalancedChannel]

/--
"Table soundness" means that we can prove the spec for each table,
assuming constraints and the partial balance assumption.
This is just Soundness, except for per-table soundness implying global soundness.
-/
@[circuit_norm]
def TableSoundness (ens : Ensemble F PublicIO) (finished : List (RawChannel F)) : Prop :=
  ∀ (witness : EnsembleWitness ens),
    witness.Constraints →
    witness.PartialBalancedChannels finished →
    ∀ table ∈ witness.allTables, table.Spec

@[circuit_norm]
abbrev SoundChannels (ens : Ensemble F PublicIO) (finished : List (RawChannel F)) : Prop :=
  -- TODO: make the verifier table use witness instead of public input, so that
  -- we can state properties about it at the static level
  _root_.SoundChannels ens.allTables finished

@[circuit_norm]
abbrev OrderedChannels (ens : Ensemble F PublicIO) (finished : List (RawChannel F)) : Prop :=
  ∀ channel ∈ finished, OrderedChannel channel ens.allTables

/--
Main result of this section:
`SoundChannels` (an easily checkable property) implies
`TableSoundness`, a complex ensemble-level soundness statement.
-/
theorem tableSoundness_of_soundChannels {ens : Ensemble F PublicIO} {finished : List (RawChannel F)} :
    ens.SoundChannels finished → ens.TableSoundness finished := by
  intro soundChannels witness constraints partial_balance table h_table
  apply spec_and_guarantees_of_soundChannels ?soundChannels ?constraints
    partial_balance table h_table |>.left
  <;> (simp only [circuit_norm]; assumption)

def channelsWithGuarantees (ens : Ensemble F PublicIO) : List (RawChannel F) :=
  ens.allTables.flatMap (·.circuit.channelsWithGuarantees)

def channelsWithRequirements (ens : Ensemble F PublicIO) : List (RawChannel F) :=
  ens.allTables.flatMap (·.circuit.channelsWithRequirements)

lemma channelsWithGuarantees_eq_verifier_append (ens : Ensemble F PublicIO) :
  ens.channelsWithGuarantees = ens.verifier.channelsWithGuarantees ++ ens.tables.flatMap (·.circuit.channelsWithGuarantees) := by
  simp [channelsWithGuarantees, allTables, verifierTable]

lemma channelsWithRequirements_eq_verifier_append (ens : Ensemble F PublicIO) :
  ens.channelsWithRequirements = ens.verifier.channelsWithRequirements ++ ens.tables.flatMap (·.circuit.channelsWithRequirements) := by
  simp [channelsWithRequirements, allTables, verifierTable]

@[circuit_norm]
lemma channelsWithGuarantees_subset_iff {ens : Ensemble F PublicIO} {finished : List (RawChannel F)} :
  ens.channelsWithGuarantees ⊆ finished ↔
    ∀ tables ∈ ens.allTables, tables.circuit.channelsWithGuarantees ⊆ finished := by
  simp [circuit_norm, channelsWithGuarantees]

/-- specs on all tables + verifier spec imply ensemble spec -/
def SpecConsistency (ens : Ensemble F PublicIO) : Prop :=
  ∀ (witness : EnsembleWitness ens),
    -- TODO maybe we could add balanced channels + channel reqs / grts here as well, to enable you to prove
    -- something at the global level from the max interaction length, like we do below for fibonacci
    -- where we prove the counter does not overflow.
    -- but it's awkward that the public input is not clearly related to the channel, only via the verifier circuit.
    -- which shows that "circuit" probably isn't the best way to model the verifier.
    (∀ table ∈ witness.allTables, table.Spec) →
    ens.Spec witness.publicInput

theorem soundness_of_tableSoundness_and_specConsistency (ens : Ensemble F PublicIO) :
  (∃ finished : List (RawChannel F), finished ⊆ ens.channels ∧ ens.TableSoundness finished) →
    ens.SpecConsistency →
    ens.Soundness := by
  simp only [Soundness, TableSoundness, SpecConsistency]
  rintro ⟨finished, finished_subset, table_soundness⟩ spec_consistency witness balance constraints
  have table_soundness := table_soundness witness constraints ?partialBalance
  apply spec_consistency witness
  · simp_all
  intro channel h_channel
  apply partialBalancedChannel_of_balancedChannel
  exact (balance channel (finished_subset h_channel))

/-- Empty ensemble satisfies SoundChannels -/
theorem empty_soundChannels : (empty F PublicIO).SoundChannels [] := by
  simp only [circuit_norm]

/-- Empty ensemble satisfies TableSoundness -/
theorem empty_tableSoundness : (empty F PublicIO).TableSoundness [] :=
  tableSoundness_of_soundChannels empty_soundChannels

end Ensemble

-- adding one table to a SoundChannels ensemble preserves SoundChannels under some
-- easy-to-prove assumptions on what channels the new table uses

namespace Ensemble
/-- Takes verifier and spec from the second ensemble -/
def merge (ens1 ens2 : Ensemble F PublicIO) : Ensemble F PublicIO :=
  { ens2 with
    tables := ens2.tables ++ ens1.tables,
    channels := ens2.channels ++ ens1.channels }

@[circuit_norm] lemma merge_tables (ens1 ens2 : Ensemble F PublicIO) :
  (ens1.merge ens2).tables = ens2.tables ++ ens1.tables := rfl
@[circuit_norm] lemma merge_verifierTable (ens1 ens2 : Ensemble F PublicIO) :
  (ens1.merge ens2).verifierTable = ens2.verifierTable := rfl

lemma mergeEnsemble_witness (ens1 ens2 : Ensemble F PublicIO)
  (witness : EnsembleWitness (ens1.merge ens2)) :
    ∃ (witness1 : EnsembleWitness ens1) (witness2 : EnsembleWitness ens2),
      witness.tables = witness2.tables ++ witness1.tables ∧
      witness1.tables = witness.tables.drop ens2.tables.length ∧
      witness2.tables = witness.tables.take ens2.tables.length ∧
      witness1.publicInput = witness.publicInput ∧
      witness2.publicInput = witness.publicInput ∧
      witness1.data = witness.data ∧
      witness2.data = witness.data := by
  have h_len : (ens1.merge ens2).tables.length = ens2.tables.length + ens1.tables.length := by
    simp [merge]
  have h_witlen : witness.tables.length = ens2.tables.length + ens1.tables.length := by
    simp [←witness.same_length, merge]
  let witness1 : EnsembleWitness ens1 := {
    tables := witness.tables.drop ens2.tables.length,
    publicInput := witness.publicInput,
    data := witness.data,
    same_length := by simp [List.length_drop, h_witlen],
    same_circuits := by
      intro i hi
      have : ens2.tables.length + i < (ens1.merge ens2).tables.length := by linarith
      simp [← witness.same_circuits _ this, merge]
    same_data := by
      intro table h_table
      apply witness.same_data
      apply List.mem_of_mem_drop h_table
  }
  let witness2 : EnsembleWitness ens2 := {
    tables := witness.tables.take ens2.tables.length,
    publicInput := witness.publicInput,
    data := witness.data,
    same_length := by simp [List.length_take, h_witlen],
    same_circuits := by
      intro i hi
      have : i < (ens1.merge ens2).tables.length := by linarith
      rw [List.getElem_take, ← witness.same_circuits _ this]
      simp [merge, hi]
    same_data := by
      intro table h_table
      apply witness.same_data
      apply List.mem_of_mem_take h_table
  }
  use witness1, witness2
  simp [witness1, witness2]

def addTable (ens : Ensemble F PublicIO) (table : AbstractTable F) : Ensemble F PublicIO :=
  { ens with tables := table :: ens.tables }

@[circuit_norm] lemma addTable_tables (ens : Ensemble F PublicIO) (table : AbstractTable F) :
  (ens.addTable table).tables = table :: ens.tables := rfl
@[circuit_norm] lemma addTable_verifierTable (ens : Ensemble F PublicIO) (table : AbstractTable F) :
  (ens.addTable table).verifierTable = ens.verifierTable := rfl
@[circuit_norm] lemma addTable_verifier (ens : Ensemble F PublicIO) (table : AbstractTable F) :
  (ens.addTable table).verifier = ens.verifier := rfl

lemma addTable_witness (ens : Ensemble F PublicIO) (table : AbstractTable F)
  (witness : EnsembleWitness (ens.addTable table)) :
    ∃ (witness' : EnsembleWitness ens) (tableWitness : TableWitness F),
      witness.tables = tableWitness :: witness'.tables ∧
      witness.publicInput = witness'.publicInput ∧
      witness.data = witness'.data ∧
      table = tableWitness.abstract ∧
      witness.data = tableWitness.data := by
  have h_len : (ens.addTable table).tables.length = ens.tables.length + 1 := by
    simp [addTable]
  have h_witlen : witness.tables.length = ens.tables.length + 1 := by
    simp [←witness.same_length, addTable]
  let witness' : EnsembleWitness ens := {
    tables := witness.tables.tail,
    publicInput := witness.publicInput,
    data := witness.data,
    same_length := by simp only [List.length_tail]; omega,
    same_circuits := by
      intro i hi
      rw [List.getElem_tail, ← witness.same_circuits]
      simp [addTable]
      simp [addTable, hi]
    same_data := by
      intro table h_table
      apply witness.same_data
      apply List.mem_of_mem_tail h_table
  }
  have h_wit_len_pos : 0 < witness.tables.length := by simp [h_witlen]
  have h_wit_ne_nil : witness.tables ≠ [] := List.ne_nil_of_length_pos h_wit_len_pos
  have h_lt : 0 < (ens.addTable table).tables.length := by simp [addTable]
  let tableWitness : TableWitness F := witness.tables.head h_wit_ne_nil
  use witness', tableWitness
  rw [witness.tables.cons_head_tail]
  simp only [tableWitness, List.head_eq_getElem]
  rw [← witness.same_circuits _ h_lt]
  have : witness.tables[0] ∈ witness.tables := by simp
  simp [addTable, witness', witness.same_data _ this]

theorem orderedChannels_of_soundChannels_addTable (ens : Ensemble F PublicIO) (table : AbstractTable F) {finished : List (RawChannel F)} :
    -- given a sound channels ensemble with empty verifier,
    ens.SoundChannels finished →
    ens.verifier = .empty F PublicIO →
    -- assuming that the new table's channelsWithGuarantees are all finished
    table.circuit.channelsWithGuarantees ⊆ finished →
    -- and that the table's channelsWithRequirements contain none of the finished ones
    -- (so that we don't get new requirements to prove)
    (∀ channel ∈ finished, channel ∉ table.circuit.channelsWithRequirements) →
    -- the ensemble with the new table also satisfies SoundChannels!
    (ens.addTable table).OrderedChannels finished := by
  intro h_sound verifier_empty grts_subset_finished reqs_disjoint_finished channel h_channel
  -- we need to make use of soundness of the original ensemble; that'll give us most of what we need
  simp only [circuit_norm, allTables, verifier_empty] at h_sound ⊢
  -- proof is a trivial combination of the hypotheses
  simp_all

theorem orderedChannels_of_soundChannels_merge (ens1 ens2 : Ensemble F PublicIO) {finished : List (RawChannel F)} :
    -- given a sound channels ensemble with empty verifier,
    ens1.SoundChannels finished →
    ens1.verifier = .empty F PublicIO →
    -- assuming that the new tables' channelsWithRequirements contain none of the finished channels
    (∀ channel ∈ finished, channel ∉ ens2.channelsWithRequirements) →
    -- the merged ensemble with the new table satisfies OrderedChannels!
    (ens1.merge ens2).OrderedChannels finished := by
  intro h_sound verifier_empty reqs_disjoint_finished channel h_channel
  simp only [circuit_norm, allTables, verifier_empty] at h_sound ⊢
  simp only [channelsWithRequirements_eq_verifier_append, circuit_norm] at reqs_disjoint_finished
  simp_all only [not_false_eq_true, or_true, true_and, and_true]
  constructor
  · apply orderedChannel_of_no_requirements
    simp_all
  · apply orderedChannelLt_of_no_requirements
    simp_all

theorem soundChannels_markFinished (ens : Ensemble F PublicIO)
    -- given a sound channels ensemble with a list of finished channels
    {finished : List (RawChannel F)} (h_sound : ens.SoundChannels finished)
    -- and given a new consistent channel to mark as finished
    (channel : RawChannel F) [channel.Consistent] :
    -- the ensemble also satisfies SoundChannels including the new channel in the finished list
    ens.SoundChannels (channel :: finished) := by
  exact soundChannels_cons_of_soundChannels h_sound
end Ensemble

structure SoundEnsemble (F : Type) [Field F] [DecidableEq F] (PublicIO : TypeMap) [ProvableType PublicIO]
    extends ensemble : Ensemble F PublicIO where
  finished : List (RawChannel F)
  finished_consistent : ∀ channel ∈ finished, channel.Consistent
  finished_subset : finished ⊆ channels
  subset_finished : ensemble.channelsWithGuarantees ⊆ finished
  ordered_channels : ensemble.OrderedChannels finished
  verifier_empty : ensemble.verifier = .empty F PublicIO
  specConsistency : ensemble.SpecConsistency

attribute [circuit_norm] SoundEnsemble.finished_consistent SoundEnsemble.finished_subset SoundEnsemble.subset_finished
  SoundEnsemble.ordered_channels SoundEnsemble.verifier_empty SoundEnsemble.specConsistency

namespace SoundEnsemble
lemma soundChannels (ens : SoundEnsemble F PublicIO) : ens.SoundChannels ens.finished := by
  rcases ens with ⟨ ens, finished, finished_consistent, finished_subset, subset_finished, ordered_channels, verifier_empty, specConsistency ⟩
  rw [ens.channelsWithGuarantees_subset_iff] at subset_finished
  simp_all only [circuit_norm]

def empty (F : Type) [Field F] [DecidableEq F] (PublicIO : TypeMap) [ProvableType PublicIO] :
  SoundEnsemble F PublicIO where
    ensemble := .empty F PublicIO
    finished := []
    finished_consistent := by simp
    finished_subset := List.Subset.refl _
    subset_finished := by simp [circuit_norm, Ensemble.channelsWithGuarantees]
    ordered_channels := by simp [circuit_norm]
    verifier_empty := by simp [circuit_norm]
    specConsistency := by
      simp only [circuit_norm, Ensemble.SpecConsistency, Ensemble.empty, FormalCircuitWithInteractions.empty]

@[circuit_norm] lemma empty_tables : (empty F PublicIO).tables = [] := rfl
@[circuit_norm] lemma empty_channels : (empty F PublicIO).channels = [] := rfl
@[circuit_norm] lemma empty_finished : (empty F PublicIO).finished = [] := rfl

def addTable (soundEns : SoundEnsemble F PublicIO) (table : AbstractTable F)
    (grts_subset_finished : table.circuit.channelsWithGuarantees ⊆ soundEns.finished
      := by simp [circuit_norm])
    (reqs_disjoint_finished : ∀ channel ∈ soundEns.finished, channel ∉ table.circuit.channelsWithRequirements
      := by simp [circuit_norm])
    : SoundEnsemble F PublicIO where
  ensemble := soundEns.ensemble.addTable table
  finished := soundEns.finished
  finished_consistent := soundEns.finished_consistent
  finished_subset := soundEns.finished_subset
  subset_finished := by
    have h := soundEns.subset_finished
    simp_all [circuit_norm, Ensemble.channelsWithGuarantees_eq_verifier_append]
  ordered_channels := soundEns.orderedChannels_of_soundChannels_addTable table soundEns.soundChannels
    soundEns.verifier_empty grts_subset_finished reqs_disjoint_finished
  verifier_empty := soundEns.verifier_empty
  specConsistency := by
    simp only [circuit_norm, Ensemble.SpecConsistency]
    intro witness spec
    obtain ⟨ witness', tableWitness, h_split, h_pi, h_data_eq, h_table, h_data_eq' ⟩ := soundEns.ensemble.addTable_witness table witness
    rw [h_pi]
    apply soundEns.specConsistency witness'
    rw [EnsembleWitness.forall_mem_allTables_iff] at spec ⊢
    simp_all only [List.mem_cons, forall_eq_or_imp, implies_true, and_true]
    convert spec.1 using 1
    apply Ensemble.verifierTable_ext <;> simp [*, Ensemble.addTable]

variable {soundEns : SoundEnsemble F PublicIO} {table : AbstractTable F}
    {gsf : table.circuit.channelsWithGuarantees ⊆ soundEns.finished}
    {rdf : ∀ channel ∈ soundEns.finished, channel ∉ table.circuit.channelsWithRequirements}

@[circuit_norm] lemma addTable_tables :
  (soundEns.addTable table gsf rdf).tables = table :: soundEns.tables := rfl

@[circuit_norm] lemma addTable_channels :
  (soundEns.addTable table gsf rdf).channels = soundEns.channels := rfl

@[circuit_norm] lemma addTable_finished :
  (soundEns.addTable table gsf rdf).finished = soundEns.finished := rfl

def addChannel (soundEns : SoundEnsemble F PublicIO) (channel : RawChannel F) : SoundEnsemble F PublicIO where
  ensemble := { soundEns.ensemble with channels := channel :: soundEns.channels }
  finished := soundEns.finished
  finished_consistent := soundEns.finished_consistent
  finished_subset := by simp [soundEns.finished_subset]
  subset_finished := soundEns.subset_finished
  ordered_channels := soundEns.ordered_channels
  verifier_empty := soundEns.verifier_empty
  specConsistency := by
    intro witness spec
    let witness' : EnsembleWitness soundEns.ensemble := { witness with }
    apply soundEns.specConsistency witness' spec

@[circuit_norm] lemma addChannel_channels {channel : RawChannel F} :
  (soundEns.addChannel channel).channels = channel :: soundEns.channels := rfl

@[circuit_norm] lemma addChannel_tables {channel : RawChannel F} :
  (soundEns.addChannel channel).tables = soundEns.tables := rfl

@[circuit_norm] lemma addChannel_finished {channel : RawChannel F} :
  (soundEns.addChannel channel).finished = soundEns.finished := rfl

def markFinished (soundEns : SoundEnsemble F PublicIO) (channel : RawChannel F) [channel.Consistent]
  (h_mem : channel ∈ soundEns.channels := by simp [circuit_norm]) :
    SoundEnsemble F PublicIO where
  ensemble := soundEns.ensemble
  finished := channel :: soundEns.finished
  finished_consistent := by
    intro channel' h_mem_channel
    rw [List.mem_cons] at h_mem_channel
    rcases h_mem_channel with rfl | h_mem_tail
    · assumption
    · exact soundEns.finished_consistent channel' h_mem_tail
  finished_subset := by simp [h_mem, soundEns.finished_subset]
  subset_finished := by simp [soundEns.subset_finished]
  ordered_channels := by
    intro channel' hc
    have : channel'.Consistent := by
      simp at hc
      rcases hc with rfl | hc_tail
      · assumption
      · exact soundEns.finished_consistent channel' hc_tail
    have := soundEns.ensemble.soundChannels_markFinished soundEns.soundChannels channel'
    exact this.right.left channel' (by simp)
  verifier_empty := soundEns.verifier_empty
  specConsistency := by apply soundEns.specConsistency

variable {channel : RawChannel F} [RawChannel.Consistent channel] {h_mem : channel ∈ soundEns.channels}

@[circuit_norm] lemma markFinished_channels :
  (soundEns.markFinished channel h_mem).channels = soundEns.channels := rfl

@[circuit_norm] lemma markFinished_tables :
  (soundEns.markFinished channel h_mem).tables = soundEns.tables := rfl

@[circuit_norm] lemma markFinished_finished :
  (soundEns.markFinished channel h_mem).finished = channel :: soundEns.finished := rfl

def addFinishedChannel (soundEns : SoundEnsemble F PublicIO) (channel : RawChannel F)
  [RawChannel.Consistent channel] : SoundEnsemble F PublicIO :=
  soundEns
    |>.addChannel channel
    |>.markFinished channel

@[circuit_norm] lemma addFinishedChannel_channels {channel : RawChannel F} [RawChannel.Consistent channel] :
  (soundEns.addFinishedChannel channel).channels = channel :: soundEns.channels := rfl

@[circuit_norm] lemma addFinishedChannel_tables {channel : RawChannel F} [RawChannel.Consistent channel] :
  (soundEns.addFinishedChannel channel).tables = soundEns.tables := rfl

@[circuit_norm] lemma addFinishedChannel_finished {channel : RawChannel F} [RawChannel.Consistent channel] :
  (soundEns.addFinishedChannel channel).finished = channel :: soundEns.finished := rfl
end SoundEnsemble

/-
VM-like ensembles have a "main channel" that stores the VM state, which we'll call a _VM channel_.
One or more tables pull from, then push to, this channel in their row circuit;
thereby performing one VM transition.

The public input/output of such an ensemble is the initial push (initial state) and the final pull (final state).
The statement being proven is that there exists a sequence of valid VM transitions from the initial state to the final state.
Note that this does not, in general, requires that every row in the trace participates in the valid VM transition!
In addition to the valid main transition path, there can be additional cycles of VM steps.

In fact, from the assumptions (constraints + balance), we _cannot_ prove `SoundChannels` for a VM channel in the sense that
all guarantees for that channel must hold. For the case of unused cycles, we have a circular implication
sequence of the form guarantees → requirements → guarantees → ... which allows that none of the guarantees are actually satisified.

This is why we need a weaker statement about VM channels which still allows us to prove soundness of the overall ensemble.
Essentially, it amounts to the simple idea that for any cycle, if just _one_ of the guarantees or requirements hold,
then all of them do.
This holds in a very general sense and is applied to the "cycle" which contains the input + output interactions.
Thus, assuming the input satisfies the requirements, we can conclude that the output satisfies the guarantees. This
can usually be engineered to be just the statement we actually care about.

These ideas are captured by the following definitions and theorems.
-/

/--
Useful mechanical lemma: if all multiplicities for a given message are the same,
the balance sum can be written as multiplicity times message count.
-/
lemma balanceOf_eq_of_const_mult {interactions : List (Interaction F)} {msg : Array F} {mult : F} :
    (∀ i ∈ interactions, i.msg = msg → i.mult = mult) →
    balanceOf interactions msg = mult * ↑(interactions.countP (·.msg = msg)) := by
  intro constant_mult
  set count : ℕ := interactions.countP (·.msg = msg)
  suffices (interactions.filter (·.msg = msg)).map (·.mult) = List.replicate count mult by
    convert (congrArg List.sum this)
    simp [mul_comm]
  apply List.ext_getElem
  · simp [count, List.countP_eq_length_filter]
  intro i hi hi'
  simp only [List.getElem_map, List.getElem_replicate]
  rw [List.length_map] at hi
  set a := (interactions.filter (·.msg = msg))[i] with ha
  have a_mem_filter : a ∈ interactions.filter (·.msg = msg) := by simp [a]
  simp only [List.mem_filter, decide_eq_true_eq] at a_mem_filter
  apply constant_mult a <;> simp_all

/--
Special case of `balanceOf_eq_of_const_mult` for when the exact message doesn't matter.
-/
lemma balanceOf_eq_of_const_mult' {interactions : List (Interaction F)} {msg : Array F} {mult : F} :
    (∀ i ∈ interactions, i.mult = mult) →
    balanceOf interactions msg = mult * ↑(interactions.countP (·.msg = msg)) :=
  fun constant_mult => balanceOf_eq_of_const_mult (fun i hi _ => constant_mult i hi)

/--
If an interaction list is balanced, then for every pull there must be a corresponding "push",
where "push" means an interaction with multiplicity ≠ -1.
-/
theorem exists_push_of_pull (interactions : List (Interaction F)) (balance : BalancedInteractions interactions) :
    ∀ a ∈ interactions, a.mult = -1 → ∃ b ∈ interactions, b.msg = a.msg ∧ b.mult ≠ -1 := by
  intro a h_mem_a h_pull
  set msg := a.msg
  set count : ℕ := (interactions.countP (·.msg = msg))
  have count_lt_ringChar : count < ringChar F ∨ ringChar F = 0 := msgInteractions_lt_ringChar balance
  replace balance := balance.2 msg
  -- assuming no such push exists => all interactions with the same message have multiplicity -1
  -- this leads to a contradiction with the 0 balance + no overflow
  by_contra! const_minus_one
  suffices count = 0 by
    simp only [count, msg, List.countP_eq_zero, decide_eq_true_eq] at this
    nomatch this a h_mem_a
  rw [balanceOf_eq_of_const_mult const_minus_one, neg_mul, one_mul, neg_eq_zero] at balance
  change (count : F) = 0 at balance
  rcases count_lt_ringChar with count_lt_ringChar | ringChar_zero
  · simp_all [Lean.Grind.IsCharP.natCast_eq_zero_iff_of_lt _ count_lt_ringChar]
  · simp_all [CharP.ringChar_zero_iff_CharZero]

/--
A "normal" channel is one where
- the requirements for a push interaction imply the guarantees of the corresponding pull interaction
- only pull interactions cause guarantees to be added
- only push interactions cause requirements to be added
-/
class NormalChannel.Raw (channel : RawChannel F) : Prop where
  grts_of_reqs : ∀ (msg : Vector F channel.arity) (mult : F) data, mult ≠ -1 →
    channel.Requirements mult msg data → channel.Guarantees (-1) msg data
  grts_of_ne_neg_one : ∀ (msg : Vector F channel.arity) (mult : F) data, mult ≠ -1 →
    channel.Guarantees mult msg data
  reqs_neg_one : ∀ (msg : Vector F channel.arity) (data), channel.Requirements (-1) msg data

class NormalChannel (channel : Channel F Message) : Prop where
  grts_of_reqs : ∀ (msg : Message F) (mult : F) data, mult ≠ -1 →
    channel.Requirements mult msg data → channel.Guarantees (-1) msg data
  grts_of_ne_neg_one : ∀ (msg : Message F) (mult : F) data, mult ≠ -1 →
    channel.Guarantees mult msg data
  reqs_neg_one : ∀ (msg : Message F) (data), channel.Requirements (-1) msg data

instance (channel : Channel F Message) [NormalChannel channel] : NormalChannel.Raw channel.toRaw where
  grts_of_reqs := by
    intro msg mult data mult_ne_neg_one reqs
    apply NormalChannel.grts_of_reqs (fromElements msg) _ _ mult_ne_neg_one reqs
  grts_of_ne_neg_one := by
    intro msg mult data mult_ne_neg_one
    apply NormalChannel.grts_of_ne_neg_one (fromElements msg) _ _ mult_ne_neg_one
  reqs_neg_one := by
    intro msg
    apply NormalChannel.reqs_neg_one (fromElements msg)

/-- Normal channels are consistent, thanks to `exists_push_of_pull` -/
theorem normalChannel_consistent (channel : RawChannel F) [NormalChannel.Raw channel] : channel.Consistent := by
  constructor
  intro interactions data balance reqs a a_mem
  simp only [Interaction.Guarantees, Interaction.Requirements, Interaction.msgVector] at reqs ⊢
  intro _
  have a_channel_eq := reqs a a_mem |>.left
  have a_msg_size : a.msg.size = channel.arity := by rw [a.same_size, a_channel_eq]
  -- we need to prove the guarantees for a given interaction from the requirements of _all_ interactions
  suffices channel.Guarantees a.mult ⟨ a.msg, a_msg_size ⟩ data by convert this
  by_cases a_mult : a.mult = -1
  -- if the multiplitity is not -1, this is trivial by `grts_of_ne_neg_one`
  case neg => exact NormalChannel.Raw.grts_of_ne_neg_one ⟨ a.msg, a_msg_size ⟩ a.mult data a_mult
  -- if the multiplicity is -1, we get the corresponding push interaction and apply `grts_of_reqs`
  rw [a_mult]
  have ⟨ b, b_mem, b_msg_eq, b_mult_ne_neg_one ⟩ := exists_push_of_pull interactions balance a a_mem a_mult
  apply NormalChannel.Raw.grts_of_reqs ⟨ a.msg, a_msg_size ⟩ b.mult data b_mult_ne_neg_one
  have ⟨ b_channel_eq, b_reqs ⟩ := reqs _ b_mem
  symm at b_channel_eq
  simp only [b_msg_eq] at b_reqs
  convert b_reqs

instance (channel : RawChannel F) [NormalChannel.Raw channel] : channel.Consistent :=
  normalChannel_consistent channel

omit [DecidableEq F] in
lemma one_ne_neg_one [Fact (ringChar F ≠ 2)] : (1 : F) ≠ -1 :=
  Ne.symm (Ring.neg_one_ne_one_of_char_ne_two ‹Fact (ringChar F ≠ 2)›.out)

-- Missing stlib lemma needed below
lemma List.countP_eraseIdx {α : Type} {l : List α} {p : α → Bool} {i : ℕ} (hi : i < l.length) :
    (l.eraseIdx i).countP p = l.countP p - (if p l[i] then 1 else 0) := by
  suffices (l.eraseIdx i).countP p + (if p l[i] then 1 else 0) = l.countP p by omega
  induction l generalizing i with
  | nil => nomatch hi
  | cons a l ih =>
    cases i with
    | zero => simp [countP_cons]
    | succ i =>
      simp only [eraseIdx_cons_succ, countP_cons, getElem_cons_succ]
      rw [← ih (Nat.lt_of_succ_lt_succ hi)]
      ring

/--
Assume you have a list of channel interactions that is made up of pairs (-1, pull_i), (1, push_i),
where for each i, Guarantees (-1, pull_i) → Requirements (1, push_i).
We want to think of (pull_i → push_i) as the state transition of a VM circuit.

Furthermore, assume the list is balanced and the channel is normal.

Then, for any i, the **converse** is true: Requirements (1, push_i) → Guarantees (-1, pull_i).
-/
theorem pairwise_guarantees_of_requirements_of_constraints [Fact (ringChar F ≠ 2)]
    (channel : RawChannel F) [NormalChannel.Raw channel]
    (pulls pushes : List (Interaction F)) (balance : BalancedInteractions (pulls ++ pushes)) (data : ProverData F)
  -- same length
  (n : ℕ) (len_pulls : pulls.length = n) (len_pushes : pushes.length = n)
  -- all interactions are on the input channel
  (pulls_channel : ∀ a ∈ pulls, a.channel = channel) (pushes_channel : ∀ b ∈ pushes, b.channel = channel)
  -- the multiplicities are -1 for pulls and 1 for pushes
  (pulls_mult : ∀ a ∈ pulls, a.mult = -1) (pushes_mult : ∀ b ∈ pushes, b.mult = 1) :
    (∀ (i : ℕ) (hi : i < n), pulls[i].Guarantees data → pushes[i].Requirements data) →
    ∀ (i : ℕ) (hi: i < n), pushes[i].Requirements data → pulls[i].Guarantees data := by
  -- the intuition for this proof is that when the requirements for b hold unconditionally, then
  -- the transition cycle that contains both a and b is valid, so in fact all the guarantees/requirements in this cycle must hold.
  -- but we avoid explicitly reasoning about cycles by using a clever inductive argument.
  intro constraints
  induction n generalizing pulls pushes with
  | zero => intro i hi; nomatch hi
  | succ n ih =>
    -- first, a little inline version of `exists_push_of_pull`
    have exists_push_of_pull : ∀ pull ∈ pulls, ∃ push ∈ pushes, push.msg = pull.msg := by
      intro pull pull_mem
      have pull_mem_append : pull ∈ pulls ++ pushes := by simp [pull_mem]
      have ⟨ push, push_mem, push_msg_eq, push_mult_ne_neg_one ⟩ := exists_push_of_pull (pulls ++ pushes)
        balance pull pull_mem_append (pulls_mult pull pull_mem)
      have push_mem : push ∈ pushes := by simp only [List.mem_append] at push_mem; tauto
      exists push
    -- we identify the "previous" transition (pulls[j], pushes[j]) in the chain, where pushes[j] = pulls[i]
    intro i hi push_i_req
    have ⟨ push', push'_mem, push_j_msg ⟩ := exists_push_of_pull pulls[i] (List.getElem_mem ..)
    set msg := pulls[i].msg with pull_i_msg
    have ⟨ j, hj, hpush' ⟩ := List.getElem_of_mem push'_mem
    subst hpush'
    rw [len_pushes] at hj
    -- thanks to the channel being consistent, it suffices to show the requirements of pushes[j]
    have push_j_imp_pull_i : pushes[j].Requirements data → pulls[i].Guarantees data := by
      intro push_j_req
      have pulls_i_channel := pulls_channel pulls[i] (List.getElem_mem ..)
      have pushes_j_channel := pushes_channel pushes[j] (List.getElem_mem ..) |>.symm
      have pulls_i_mult := pulls_mult pulls[i] (List.getElem_mem ..)
      have pushes_j_mult := pushes_mult pushes[j] (List.getElem_mem ..) |>.symm
      have msg_size : msg.size = channel.arity := by rw [pulls[i].same_size, pulls_i_channel]
      suffices grt' : channel.Guarantees (-1) ⟨ msg, msg_size ⟩ data by
        simp only [Interaction.Guarantees]
        convert fun _ => grt'
      apply NormalChannel.Raw.grts_of_reqs ⟨ msg, msg_size ⟩ 1 data one_ne_neg_one
      simp only [Interaction.Requirements, Interaction.msgVector, push_j_msg] at push_j_req
      convert push_j_req
    -- if i = j, we're done
    by_cases h_ij : j = i
    · subst h_ij; exact push_j_imp_pull_i push_i_req
    -- if i ≠ j, we can reduce our goal to a smaller list: the one where
    -- (pulls[j], pushes[j]) and (pulls[i], pushes[i]) are replaced with the single pair (pulls[j], pushes[i]).
    have pulls_j_imp_push_i : pulls[j].Guarantees data → pushes[i].Requirements data := fun j_grt =>
      j_grt |> constraints j hj |> push_j_imp_pull_i |> constraints i hi
    -- we remove (pulls[i], pushes[i]) and change pushes[j] to pushes[i]
    let j' := if j < i then j else j - 1
    let pulls' := pulls.eraseIdx i
    let pushes' := pushes.eraseIdx i |>.set j' pushes[i]
    have hj' : j' < n := by simp only [j']; split_ifs <;> omega
    have pulls'_len : pulls'.length = n := by simp [pulls', List.length_eraseIdx, len_pulls, hi]
    have pushes'_len : pushes'.length = n := by simp [pushes', List.length_eraseIdx, len_pushes, hi]
    have pulls'_getElem : pulls'[j'] = pulls[j] := by
      simp only [pulls', j', List.getElem_eraseIdx]
      split_ifs
      · simp
      · omega
      · simp [show j - 1 + 1 = j by omega]
    have pushes'_getElem : pushes'[j'] = pushes[i] := by simp [pushes', j']
    suffices push_i_imp_pull_j : pushes'[j'].Requirements data → pulls'[j'].Guarantees data by
      simp only [pulls'_getElem, pushes'_getElem] at push_i_imp_pull_j
      exact push_i_req |> push_i_imp_pull_j |> constraints j hj |> push_j_imp_pull_i
    -- we need to re-check all assumptions about as', bs' for the induction hypothesis
    -- most of these are straightforward
    have pulls'_mult : ∀ a ∈ pulls', a.mult = -1 := by
      simp only [pulls', List.forall_mem_iff_getElem, List.getElem_eraseIdx]
      intros; split_ifs <;> simp [*]
    have pushes'_mult : ∀ b ∈ pushes', b.mult = 1 := by
      simp only [pushes', List.forall_mem_iff_getElem, List.getElem_eraseIdx, List.getElem_set]
      intros; split_ifs <;> simp [*]
    apply ih pulls' pushes' ?balance' pulls'_len pushes'_len ?pulls'_channel ?pushes'_channel pulls'_mult pushes'_mult ?constraints' j' hj'
    <;> clear ih
    case pulls'_channel | pushes'_channel =>
      simp only [pulls', pushes', List.forall_mem_iff_getElem, List.getElem_set, List.getElem_eraseIdx]
      intros; split_ifs <;> simp [*]
    case constraints' : ∀ i' (hi' : i' < n), pulls'[i'].Guarantees data → pushes'[i'].Requirements data := by
      intro i' hi'
      by_cases h_ij' : j' = i'
      · simp only [←h_ij', pulls'_getElem, pushes'_getElem]
        exact pulls_j_imp_push_i
      simp only [pulls', pushes', h_ij', List.getElem_eraseIdx, ne_eq, not_false_eq_true, List.getElem_set_ne]
      split_ifs <;> exact constraints _ (by linarith)
    -- it only remains to prove the balance condition for pulls' ++ pushes'.
    -- at a high level, this is obvious because we removed two opposing elements with the same message
    -- (pushes[j] and pulls[i]), so balance for any message is unaffected.
    rcases balance with ⟨ lt_ringChar, balance ⟩
    simp only [len_pulls, len_pushes, List.length_append] at lt_ringChar
    constructor
    · simp only [pulls'_len, pushes'_len, List.length_append]
      rcases lt_ringChar with lt_ringChar | ringChar_zero
      · left; linarith
      · right; assumption
    intro msg'
    specialize balance msg'
    simp only [balanceOf_append] at balance ⊢
    rw [balanceOf_eq_of_const_mult' pulls_mult, balanceOf_eq_of_const_mult' pushes_mult] at balance
    rw [balanceOf_eq_of_const_mult' pulls'_mult, balanceOf_eq_of_const_mult' pushes'_mult]
    simp only [neg_mul, one_mul, neg_add_eq_zero] at balance ⊢
    have count_eq : pulls.countP (·.msg = msg') = pushes.countP (·.msg = msg') := by
      rcases lt_ringChar with lt_ringChar | ringChar_zero
      · have a_lt_ringChar : pulls.countP (·.msg = msg') < ringChar F := by
          grw [List.countP_le_length, len_pulls, Nat.le_add_right (n + 1) (n + 1)]
          exact lt_ringChar
        have b_lt_ringChar : pushes.countP (·.msg = msg') < ringChar F := by
          grw [List.countP_le_length, len_pushes, Nat.le_add_right (n + 1) (n + 1)]
          exact lt_ringChar
        rw [Lean.Grind.IsCharP.natCast_eq_iff_of_lt _ a_lt_ringChar b_lt_ringChar] at balance
        exact balance
      · rw [CharP.ringChar_zero_iff_CharZero] at ringChar_zero
        rw [Nat.cast_inj] at balance
        exact balance
    have pushes_eq : pushes' = (pushes.set j pushes[i]).eraseIdx i := by
      simp [pushes', List.eraseIdx_set, j']
      split_ifs <;> (simp_all; try omega)
    simp only [pulls', pushes_eq]
    rw [List.countP_eraseIdx (by linarith), ←pull_i_msg]
    rw [List.countP_eraseIdx (by simp_all), List.countP_set (len_pushes ▸ hj), push_j_msg]
    simp [h_ij, count_eq]

/--
Soundness for a VM ensemble is simple:
- the ensemble spec is just the verifier spec
- the verifier spec can be proven from constraints + balance for all tables/channels
-/
def Ensemble.SoundVmChannel (ens : Ensemble F PublicIO) : Prop :=
  ∀ (witness : EnsembleWitness ens),
    witness.Constraints →
    witness.BalancedChannels →
      ens.VerifierGuarantees witness.publicInput witness.data

structure SoundVmEnsemble (F : Type) [Field F] [DecidableEq F] (PublicIO : TypeMap) [ProvableType PublicIO]
    extends ensemble : Ensemble F PublicIO where
  spec_eq publicInput : ensemble.Spec publicInput = ∃ data, ensemble.VerifierSpec publicInput data := by intros; rfl
  soundVmChannel : ensemble.SoundVmChannel

theorem SoundVmEnsemble.soundness (ens : SoundVmEnsemble F PublicIO) : ens.Soundness := by
  intro witness balance constraints
  rw [ens.spec_eq]
  use witness.data
  have soundVm := ens.soundVmChannel
  simp only [Ensemble.SoundVmChannel, Ensemble.VerifierGuarantees,
    Ensemble.VerifierSpec, EnsembleWitness.Constraints] at *
  specialize soundVm witness constraints balance
  convert (ens.verifier.original_full_soundness _ _ _ ?_ soundVm).1
  · rw [ProvableType.eval_fromInput_varFromOffset_zero]
  exact EnsembleWitness.verifierConstraints_of_constraints constraints

structure VmTables (F : Type) [Field F] [DecidableEq F] (PublicIO : TypeMap) [ProvableType PublicIO] where
  {Message : TypeMap} [provableMessage : ProvableType Message]
  channel : Channel F Message
  [normalChannel : NormalChannel (F:=F) channel]

  tables : List (AbstractTable F)
  verifier : FormalCircuitWithInteractions F PublicIO unit
  verifier_length_zero : ∀ pi, (verifier pi).localLength 0 = 0 := by
    simp only [circuit_norm]

  tables_channel : ∀ table ∈ tables,
    ∃ m1 m2, ⟨ channel, [(channel.pulled m1).toRaw, (channel.pushed m2).toRaw] ⟩ ∈
      table.circuit.exposedChannels table.rowInputVar table.rowOffset

  -- the verifier pulls and pushes to the channel
  verifier_channel : ∃ m1 m2, ⟨ channel, [(channel.pulled m1).toRaw, (channel.pushed m2).toRaw] ⟩ ∈
      verifier.exposedChannels (varFromOffset PublicIO 0) (size PublicIO)

  -- verifier requirements are unconditionally true
  -- TODO: this works if the initial state is fixed and statically guaranteed to fulfill the reqs
  -- but what if the state is an input and we want to add this as an assumption?
  -- => then the verifier circuit should add constraints to enforce the requirements!
  -- => this should work if the condition is formulated correctly, but the one below is too restrictive
  verifier_requirements : verifier.channelsWithRequirements = [] := by rfl

instance (vm : VmTables F PublicIO) : ProvableType vm.Message := vm.provableMessage
instance (vm : VmTables F PublicIO) : NormalChannel vm.channel := vm.normalChannel

def VmTables.toEnsemble (vm : VmTables F PublicIO) : Ensemble F PublicIO where
  channels := [vm.channel.toRaw]
  tables := vm.tables
  verifier := vm.verifier
  verifier_length_zero := vm.verifier_length_zero
  Spec publicInput := ∃ data, vm.verifier.Spec publicInput () (.fromInput publicInput data)

lemma AbstractTable.interactionsWith_of_exposedChannels {table : AbstractTable F} {channel : RawChannel F}
  {interactions : List (AbstractInteraction F)}
  (h_exposed : ⟨ channel, interactions ⟩ ∈ table.exposedChannels) :
    table.operations.interactionsWith channel = interactions := by
  rw [AbstractTable.interactionsWith_eq]
  simp only [circuit_norm, AbstractTable.exposedChannels] at *
  convert table.circuit.exposedChannels_eq _ _ _ h_exposed

def List.flattenPairs {α : Type} (pairs : List (α × α)) : List α :=
  pairs.map (fun (a, b) => [a, b]) |>.flatten

lemma flattenPairs_cons {α : Type} (a b : α) (pairs : List (α × α)) :
    List.flattenPairs ((a, b) :: pairs) = [a, b] ++ List.flattenPairs pairs := by
  simp [List.flattenPairs]

lemma zip_flattenPairs_perm {α : Type} {as bs : List α} :
    bs.length = as.length → List.Perm (List.zip as bs).flattenPairs (as ++ bs) := by
  open List in
  suffices ∀ n, as.length = n → bs.length = n →
    List.Perm (List.zip as bs).flattenPairs (as ++ bs) from this as.length rfl
  intro n as_len bs_len
  induction n generalizing as bs with
  | zero => simp_all [List.flattenPairs]
  | succ n ih =>
    rcases as with rfl | ⟨ a, as ⟩; nomatch as_len
    rcases bs with rfl | ⟨ b, bs ⟩; nomatch bs_len
    simp only [length_cons, Nat.add_right_cancel_iff] at as_len bs_len
    specialize ih as_len bs_len
    simp only [zip_cons_cons, flattenPairs_cons, cons_append, nil_append]
    grw [perm_cons, ← perm_cons_append_cons _ perm_rfl, perm_cons, ih]

/-- Instead of first map-flattening on the inside, then on the outside,
we can map to a 3D array, then flatten the outside, and only then the inside.
Good if you want to preserve the inner structure. -/
lemma flatMap_flatMap {α β γ : Type*} (l : List γ) (g : γ → List α) (f : γ → α → List β) :
  l.flatMap (fun x => (g x).flatMap (f x)) = (l.map (fun x => (g x).map (f x))).flatten.flatten := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp [ih]
    rfl

noncomputable def TableWitness.interactionssWith (table : TableWitness F)
    (channel : RawChannel F) : List (List (Interaction F)) :=
  table.table.map fun row =>
    table.abstract.operations.interactionValuesWith channel (table.environment row)

/-- Ensemble interactions preserving the per-row structure until the final flatten. -/
lemma EnsembleWitness.flatMap_interactionsWith_eq_flatten {ens : Ensemble F PublicIO}
  (witness : EnsembleWitness ens) {channel : RawChannel F} :
  witness.tables.flatMap (·.interactionsWith channel) =
    (witness.tables.flatMap (·.interactionssWith channel)).flatten := by
  simp only [TableWitness.interactionsWith, TableWitness.interactionssWith]
  rw [flatMap_flatMap, List.flatMap_def]

lemma zip_flatten_flatten {α : Type} (as bs : List (List (α)))
  (same_lengths : as.length = bs.length ∧ (∀ i (hi : i < as.length) (hi' : i < bs.length), as[i].length = bs[i].length)) :
    List.zip as.flatten bs.flatten = ((as.zip bs).map (fun (t, s) => t.zip s)).flatten := by
  revert same_lengths
  suffices ∀ n, (_ : as.length = n) → (_ : bs.length = n) →
    (∀ i (hi : i < n), as[i].length = bs[i].length) →
      List.zip as.flatten bs.flatten = ((as.zip bs).map (fun t => t.1.zip t.2)).flatten by
    rintro ⟨ same_length, same_lengths ⟩
    apply this as.length rfl same_length.symm
    intro i hi
    exact same_lengths i hi (by linarith)
  intro n alen blen same_lengths
  induction n generalizing as bs with
  | zero =>
    simp at alen blen
    simp [alen, blen]
  | succ n ih =>
    rcases as with rfl | ⟨ a, as ⟩; simp
    rcases bs with rfl | ⟨ b, bs ⟩; simp
    simp at alen blen
    have same_length_zero : a.length = b.length := same_lengths 0 (by linarith)
    have same_length_succ i (hi : i < n) : as[i].length = bs[i].length := same_lengths (i + 1) (by linarith)
    simp only [List.flatten_cons, List.zip_cons_cons, List.map_cons]
    rw [List.zip_append same_length_zero]
    specialize ih as bs alen blen same_length_succ
    rw [ih]

abbrev VmWitness (vm : VmTables F PublicIO) := EnsembleWitness vm.toEnsemble

namespace VmTables
noncomputable def tablePair (vm : VmTables F PublicIO) (table : AbstractTable F) (table_mem : table ∈ vm.tables) :
    Var vm.Message F × Var vm.Message F :=
  let h := vm.tables_channel table table_mem
  ⟨ h.choose, h.choose_spec.choose ⟩

noncomputable def tablePull (vm : VmTables F PublicIO)
  {table : AbstractTable F} (table_mem : table ∈ vm.tables) := vm.tablePair table table_mem |>.fst

noncomputable def tablePush (vm : VmTables F PublicIO)
  {table : AbstractTable F} (table_mem : table ∈ vm.tables) := vm.tablePair table table_mem |>.snd

/-- Concrete version of VmTables.tables_channel -/
lemma tables_channel' (vm : VmTables F PublicIO) {table} (_ : table ∈ vm.tables) :
  ⟨ vm.channel.toRaw,
    [(vm.channel.pulled (vm.tablePull ‹_›)).toRaw, (vm.channel.pushed (vm.tablePush ‹_›)).toRaw]
  ⟩ ∈ table.exposedChannels :=
  vm.tables_channel table ‹_›
  |>.choose_spec.choose_spec

lemma interactionsWith_eq {vm : VmTables F PublicIO} {table} (_ : table ∈ vm.tables) :
  table.operations.interactionsWith vm.channel.toRaw = [
    vm.channel.pulled (vm.tablePull ‹_›) |>.toRaw,
    vm.channel.pushed (vm.tablePush ‹_›) |>.toRaw ] := by
  apply AbstractTable.interactionsWith_of_exposedChannels
  apply vm.tables_channel'
end VmTables

namespace VmWitness
variable {vm : VmTables F PublicIO}

noncomputable def tablePull (witness : VmWitness vm) {table} (_ : table ∈ witness.tables) (row : Array F) : vm.Message F :=
  eval (table.environment row) (vm.tablePull (witness.mem_tables_abstract_of_mem_tables ‹_›))

noncomputable def tablePush (witness : VmWitness vm) {table} (_ : table ∈ witness.tables) (row : Array F) : vm.Message F :=
  eval (table.environment row) (vm.tablePush (witness.mem_tables_abstract_of_mem_tables ‹_›))

lemma interactionValuesWith_eq (witness : VmWitness vm)
    {table} (_ : table ∈ witness.tables) (row : Array F) :
  table.abstract.operations.interactionValuesWith vm.channel.toRaw (table.environment row) = [
    vm.channel.pulledValue (witness.tablePull ‹_› row),
    vm.channel.pushedValue (witness.tablePush ‹_› row) ] := by
  simp only [circuit_norm, vm.interactionsWith_eq (witness.mem_tables_abstract_of_mem_tables ‹_›),
    tablePull, tablePush, AbstractInteraction.eval, ProvableType.toElements_eval]

lemma interactionValuesWith_length (witness : VmWitness vm)
    {table} (_ : table ∈ witness.tables) (row : Array F) :
  (table.abstract.operations.interactionValuesWith vm.channel.toRaw (table.environment row)).length = 2 := by
  simp [witness.interactionValuesWith_eq ‹_› row]

noncomputable def pulls (witness : VmWitness vm) : List (Interaction F) :=
  witness.tables.attach.flatMap fun ⟨ table, _ ⟩ =>
    table.table.map fun row => vm.channel.pulledValue (witness.tablePull ‹_› row)

noncomputable def pushes (witness : VmWitness vm) : List (Interaction F) :=
  witness.tables.attach.flatMap fun ⟨ table, _ ⟩ =>
    table.table.map fun row => vm.channel.pushedValue (witness.tablePush ‹_› row)

def steps (witness : VmWitness vm) : ℕ := witness.tables.map (·.length) |>.sum

lemma length_pulls (witness : VmWitness vm) : witness.pulls.length = witness.steps := by
  simp [steps, pulls]

lemma length_pushes (witness : VmWitness vm) : witness.pushes.length = witness.steps := by
  simp [steps, pushes]

-- TODO might not need
lemma pulls_eq_interactions (witness : VmWitness vm) : witness.pulls =
  witness.tables.attach.flatMap fun ⟨ table, _ ⟩ =>
    table.table.map fun row =>
      (table.abstract.operations.interactionValuesWith vm.channel.toRaw (table.environment row))[0]'
        (by simp [witness.interactionValuesWith_eq ‹_› row]) := by
  simp only [pulls]
  congr! with ⟨ table, table_mem ⟩ row
  simp [witness.interactionValuesWith_eq ‹_› row]

-- TODO might not need
lemma pushes_eq_interactions (witness : VmWitness vm) : witness.pushes =
  witness.tables.attach.flatMap fun ⟨ table, _ ⟩ =>
    table.table.map fun row =>
      (table.abstract.operations.interactionValuesWith vm.channel.toRaw (table.environment row))[1]'
        (by simp [witness.interactionValuesWith_eq ‹_› row]) := by
  simp only [pushes]
  congr! with ⟨ table, table_mem ⟩ row
  simp [witness.interactionValuesWith_eq ‹_› row]

lemma interactionss_eq_pulls_pushes (witness : VmWitness vm) :
  witness.tables.flatMap (·.interactionssWith vm.channel.toRaw) =
    (List.zip witness.pulls witness.pushes).map (fun ⟨pull, push⟩ => [pull, push]) := by
  simp only [pulls, pushes, List.flatMap_def]
  rw [zip_flatten_flatten _ _ (by simp), List.map_flatten]
  simp only [List.zip_map', List.map_map]
  rw [← List.pmap_eq_map (fun _ _ => trivial), List.pmap_eq_map_attach]
  congr
  funext ⟨ table, table_mem ⟩
  simp [TableWitness.interactionssWith, List.zip_map',
    witness.interactionValuesWith_eq table_mem]

lemma interactions_eq_pulls_pushes (witness : VmWitness vm) :
  witness.tables.flatMap (·.interactionsWith vm.channel.toRaw) =
    (List.zip witness.pulls witness.pushes).flattenPairs := by
  rw [witness.flatMap_interactionsWith_eq_flatten,
    interactionss_eq_pulls_pushes, List.flattenPairs]

lemma mem_zip_pulls_pushes_iff (witness : VmWitness vm) (pull push : Interaction F) :
  (pull, push) ∈ List.zip witness.pulls witness.pushes ↔
    ∃ table ∈ witness.tables, ∃ row ∈ table.table,
      table.abstract.operations.interactionValuesWith vm.channel.toRaw (table.environment row) = [pull, push] := by
  trans [pull, push] ∈ (List.zip witness.pulls witness.pushes).map (fun ⟨pull, push⟩ => [pull, push])
  · simp
  simp [← interactionss_eq_pulls_pushes, TableWitness.interactionssWith]

lemma pull_properties (witness : VmWitness vm) : ∀ pull ∈ witness.pulls,
    pull.channel = vm.channel.toRaw ∧ pull.mult = -1 ∧ pull.Requirements witness.data := by
  intro pull pull_mem
  simp [pulls] at pull_mem
  obtain ⟨ table, table_mem, row, row_mem, pull_eq ⟩ := pull_mem
  symm at pull_eq; subst pull_eq
  simp only [circuit_norm, Interaction.Requirements]
  exact vm.normalChannel.reqs_neg_one _ witness.data

lemma push_properties (witness : VmWitness vm) : ∀ push ∈ witness.pushes,
    push.channel = vm.channel.toRaw ∧ push.mult = 1 ∧ push.Guarantees witness.data := by
  intro push push_mem
  simp [pushes] at push_mem
  obtain ⟨ table, table_mem, row, row_mem, push_eq ⟩ := push_mem
  symm at push_eq; subst push_eq
  simp only [circuit_norm, Interaction.Guarantees]
end VmWitness

namespace Ensemble
def addVm (ens : Ensemble F PublicIO) (vm : VmTables F PublicIO) : Ensemble F PublicIO where
  channels := vm.channel :: ens.channels
  tables := vm.tables ++ ens.tables
  verifier := vm.verifier
  verifier_length_zero := vm.verifier_length_zero
  Spec publicInput := ∃ data, vm.verifier.Spec publicInput () (.fromInput publicInput data)

@[circuit_norm] lemma addVm_channels (ens : Ensemble F PublicIO) (vm : VmTables F PublicIO) :
  (ens.addVm vm).channels = vm.channel.toRaw :: ens.channels := rfl

lemma addVm_witness (ens : Ensemble F PublicIO) (vm : VmTables F PublicIO)
  (witness : EnsembleWitness (ens.addVm vm)) :
    ∃ (vmWitness : VmWitness vm) (witness' : EnsembleWitness ens),
      witness.tables = vmWitness.tables ++ witness'.tables ∧
      witness.allTables = vmWitness.allTables ++ witness'.tables ∧
      vmWitness.publicInput = witness.publicInput ∧
      witness'.publicInput = witness.publicInput ∧
      vmWitness.data = witness.data ∧
      witness'.data = witness.data ∧
      ∀ i (hi : i < vmWitness.tables.length),
        (∃ (hi': i < vm.tables.length), vmWitness.tables[i].abstract = vm.tables[i]) ∧
        vmWitness.tables[i].data = witness.data := by
  sorry

theorem addVm_soundVmChannel_of_soundChannels [Fact (ringChar F ≠ 2)] (ens : Ensemble F PublicIO)
      -- given a sound channels ensemble with a list of finished, consistent channels
    {finished : List (RawChannel F)} (soundChannels : ens.SoundChannels finished)
    (consistent : ∀ channel ∈ finished, channel.Consistent)
    (finished_subset : finished ⊆ ens.channels)
    (verifier_empty : ens.verifier = .empty F PublicIO)
    -- and given a VM channel + tables + verifier
    (vm : VmTables F PublicIO) :
    -- assuming that none of the existing tables interacted with the VM channel
    -- TODO! we should only allow adding tables to an ensemble if the channels they interact with were already added
    -- this would simplify this proof, and provide more meaning to the .channels property
    (∀ table ∈ ens.tables, vm.channel.toRaw ∉ table.circuit.channels) →
    -- assuming that the VM tables' and verifier's channelsWithGuarantees are either finished or the VM channel
    (∀ table ∈ vm.tables, table.circuit.channelsWithGuarantees ⊆ vm.channel.toRaw :: finished) →
    vm.verifier.channelsWithGuarantees ⊆ vm.channel.toRaw :: finished →
    -- and assuming the VM tables' channelsWithRequirements contain none of the finished ones
    (∀ table ∈ vm.tables, ∀ channel ∈ finished, channel ∉ table.circuit.channelsWithRequirements) →
    -- the ensemble with the VM tables satisfies SoundVmChannel
    (ens.addVm vm).SoundVmChannel := by
  intro ne_mem_vm_channel grts_subset vgrts_subset reqs_disjoint witness constraints balance
  /-
  the high level idea is to show we are in the situation of `pairwise_guarantees_of_requirements_of_constraints`,
  where the targeted interactions are those with the VM channel: vm tables + verifier.

  the combination of constraints + guarantees for existing channels gives us the main condition:
  "vm guarantees → vm requirements".
  finally, `VmTables.verifier_requirements` gives us the requirements for the verifier, from which the conclusion follows.
  -/
  obtain ⟨ vmWitness, witness', h_tables, h_allTables, h_vm_pi, h_pi, h_vm_data, h_data, h_vmTables ⟩ :=
    addVm_witness ens vm witness
  have h_data' : vmWitness.data = witness'.data := by rw [h_data, h_vm_data]
  set vmTables := vmWitness.tables
  set vmChannel := vm.channel.toRaw
  -- instantiate `pairwise_guarantees_of_requirements_of_constraints`.
  -- first, we show that the vm channel interactions are made up of pull/push pairs
  let vmInteractions := witness.interactionsWith vmChannel
  let vmVerifier := vm.verifier.instantiate
  let vmVerifierInteractions := vm.toEnsemble.verifierOperations.interactionsWith vmChannel
    |>.map (AbstractInteraction.eval (.fromInput witness.publicInput witness.data))
  have vmVerifierInteractions_eq : vmWitness.verifierTable.interactionsWith vmChannel
      = vmVerifierInteractions := by
    simp only [circuit_norm, TableWitness.interactionsWith, vmVerifierInteractions,
      Ensemble.verifierTable_interactionsWith, h_vm_data, h_vm_pi]
  have vmInteractions_eq_vmTableInteractions :
      vmInteractions = vmWitness.allTables.flatMap (·.interactionsWith vmChannel) := by
    sorry
  have vmInteractions_eq : vmInteractions =
      vmVerifierInteractions ++ vmTables.flatMap (·.interactionsWith vmChannel) := by
    simp only [vmInteractions, EnsembleWitness.interactionsWith, h_allTables, List.flatMap_append]
    suffices witness'.tables.flatMap (·.interactionsWith vmChannel) = [] by
      rw [this, List.append_nil]
      simp [EnsembleWitness.allTables, vmVerifierInteractions_eq, vmTables]
    simp only [List.flatMap_eq_nil_iff]
    intro table mem_table
    apply TableWitness.interactionsWith_nil_of_channel_not_mem
    apply ne_mem_vm_channel table.abstract
    exact EnsembleWitness.mem_tables_abstract_of_mem_tables mem_table
  obtain ⟨ pull0Var, push0Var, vmVerifierInteractions_eq ⟩ := vm.verifier_channel
  set verifierEnv := Environment.fromInput witness.publicInput witness.data
  let pull0 := eval verifierEnv pull0Var
  let push0 := eval verifierEnv push0Var
  replace vmVerifierInteractions_eq : vmVerifierInteractions =
      [vm.channel.pulledValue pull0, vm.channel.pushedValue push0] := by
    replace vmVerifierInteractions_eq := vm.verifier.exposedChannels_eq (varFromOffset PublicIO 0) (size PublicIO) _ vmVerifierInteractions_eq
    simp only [vmVerifierInteractions] at vmVerifierInteractions_eq ⊢
    rw [←Channel.eval_pulled, ←Channel.eval_pushed]
    show _ = [(vm.channel.pulled pull0Var).toRaw, (vm.channel.pushed push0Var).toRaw].map (·.eval verifierEnv)
    congr
  rw [vmVerifierInteractions_eq] at vmInteractions_eq
  have vmInteractions_eq' := vmWitness.interactions_eq_pulls_pushes
  rw [vmInteractions_eq'] at vmInteractions_eq; clear vmInteractions_eq'
  rw [← flattenPairs_cons, ← List.zip_cons_cons] at vmInteractions_eq
  set pulls := vm.channel.pulledValue pull0 :: vmWitness.pulls
  set pushes := vm.channel.pushedValue push0 :: vmWitness.pushes
  have pairwise_guarantees := pairwise_guarantees_of_requirements_of_constraints vmChannel pulls pushes
  -- we fill in the conditions on pulls and pushes in `pairwise_guarantees`
  let n := vmWitness.steps + 1
  have pulls_len : pulls.length = n := by simp [n, pulls, vmWitness.length_pulls]
  have pushes_len : pushes.length = n := by simp [n, pushes, vmWitness.length_pushes]
  have pulls_channel : ∀ pull ∈ pulls, pull.channel = vmChannel := by
    simp [pulls, vmChannel, Channel.pulledValue]
    intro pull pull_mem
    simp [vmWitness.pull_properties pull pull_mem]
  have pushes_channel : ∀ push ∈ pushes, push.channel = vmChannel := by
    simp [pushes, vmChannel, Channel.pushedValue]
    intro push push_mem
    simp [vmWitness.push_properties push push_mem]
  have pulls_mult : ∀ pull ∈ pulls, pull.mult = -1 := by
    simp [pulls, Channel.pulledValue]
    intro pull pull_mem
    simp [vmWitness.pull_properties pull pull_mem]
  have pushes_mult : ∀ push ∈ pushes, push.mult = 1 := by
    simp [pushes, Channel.pushedValue]
    intro push push_mem
    simp [vmWitness.push_properties push push_mem]
  have vmChannel_mem : vmChannel ∈ (ens.addVm vm).channels := by simp [Ensemble.addVm, vmChannel]
  have vmBalance : BalancedInteractions (pulls ++ pushes) := by
    have originalBalance : BalancedInteractions vmInteractions := balance vmChannel vmChannel_mem
    rw [vmInteractions_eq] at originalBalance
    apply balancedInteractions_of_perm originalBalance
    apply zip_flattenPairs_perm <| pushes_len ▸ pulls_len.symm
  specialize pairwise_guarantees vmBalance witness.data n pulls_len pushes_len pulls_channel pushes_channel pulls_mult pushes_mult
  -- to use this theorem, we need guarantees for all non-vm channels to hold unconditionally, on both the new tables and the verifier!
  -- this is what `SoundChannels` for the existing ensemble gives us when we add all the new tables!
  have finished_reqs : ∀ channel ∈ finished, ∀ table ∈ witness'.allTables,
      table.ChannelRequirements channel := by
    -- this comes from soundness + constraints
    sorry
  have reqs_disjoint' : ∀ table ∈ vm.toEnsemble.allTables,
      ∀ channel ∈ finished, channel ∉ table.circuit.channelsWithRequirements := by
    simp only [circuit_norm, VmTables.toEnsemble, allTables]
    rw [vm.verifier_requirements]
    simp
    exact reqs_disjoint
  have finished_grts : ∀ table ∈ vmWitness.allTables, ∀ channel ∈ finished,
      table.ChannelGuarantees channel := by
    intro table table_mem channel channel_mem
    have : channel.Consistent := consistent channel channel_mem
    apply guarantees_of_requirements_append (ts := vmWitness.allTablesWitness)
      (ss := witness'.allTablesWitness) (same_data := h_data')
    · intro table' table'_mem
      apply reqs_disjoint' table'.abstract ?_ channel channel_mem
      apply vmWitness.mem_allTables_abstract_of_mem_allTables table'_mem
    · apply partialBalancedChannel_of_balancedInteractions
      convert balance channel ?_ using 1
      · simp only [circuit_norm]
        rw [EnsembleWitness.interactionsWith_of_verifier_empty verifier_empty]
        simp only [EnsembleWitness.interactionsWith, h_allTables, circuit_norm]
      simp only [circuit_norm]
      right
      exact finished_subset channel_mem
    · exact finished_reqs channel channel_mem
    · exact table_mem
  have vm_constraints : vmWitness.Constraints := by
    sorry
  -- unify channel subset assumption to all tables
  have subset (table : TableWitness F) (h_table : table ∈ vmWitness.allTables) :
      table.channelsWithGuarantees ⊆ vmChannel :: finished := by
    intro channel channel_mem
    replace h_table : table.abstract ∈ _ := vmWitness.mem_allTables_abstract_of_mem_allTables h_table
    simp [Ensemble.allTables, circuit_norm] at h_table channel_mem
    rcases h_table with h_ver | h_table
    · apply vgrts_subset
      rw [h_ver] at channel_mem
      convert channel_mem using 1
    · apply grts_subset table.abstract h_table channel_mem
  have vm_soundness (table : TableWitness F) (h_table : table ∈ vmWitness.allTables) :=
    table.requirements_of_partial_guarantees_of_constraints (finished := finished) (unfinished := vmChannel)
    (vm_constraints table h_table) (subset table h_table) (finished_grts table h_table)
  have vm_reqs_of_grts : (∀ i (hi : i < n),
      pulls[i].Guarantees witness.data → pushes[i].Requirements witness.data) := by
    suffices ∀ pair ∈ (pulls.zip pushes), pair.1.Guarantees witness.data → pair.2.Requirements witness.data by
      simp only [List.forall_mem_iff_getElem, List.getElem_zip] at this
      intro i hi
      exact this i (by simp [pulls_len, pushes_len, hi])
    rw [← ‹vmWitness.data = witness.data›]
    intro (pull, push) pair_mem
    simp only
    simp [pulls, pushes] at pair_mem
    rcases pair_mem with pair_mem|pair_mem
    · sorry -- verifier case
    have ⟨ mem_pull, mem_push ⟩ := List.of_mem_zip pair_mem
    have ⟨ _, _, push_grts ⟩ := vmWitness.push_properties push mem_push
    have ⟨ _, _, pull_reqs ⟩ := vmWitness.pull_properties pull mem_pull
    -- simp only [VmWitness.pulls, VmWitness.tablePull, ← Channel.eval_pulled] at mem_pull
    rw [vmWitness.mem_zip_pulls_pushes_iff] at pair_mem
    obtain ⟨ table, table_mem, row, row_mem, interactions_eq ⟩ := pair_mem
    suffices (∀ i ∈ [pull, push], i.Guarantees vmWitness.data) → (∀ i ∈ [pull, push], i.Requirements vmWitness.data) by
      simp_all
    simp only [← interactions_eq, Operations.interactionValuesWith_eq_map, List.forall_mem_map]
    have env_data_eq : (table.environment row).data = vmWitness.data := vmWitness.same_data _ table_mem
    simp only [← env_data_eq, AbstractInteraction.eval_guarantees, AbstractInteraction.eval_requirements,
      Operations.forall_interactionsWith_iff]
    specialize vm_soundness table (vmWitness.mem_allTables_of_mem_tables table_mem) row row_mem
    convert vm_soundness
  specialize pairwise_guarantees vm_reqs_of_grts 0 (by simp [n])
  simp [pulls, pushes] at pairwise_guarantees
  have := vm.verifier_requirements
  -- we are basically there, just need to insert this at pairwise_guarantees and shows that this is exactly the goal
  sorry
end Ensemble

def SoundEnsemble.addVm [Fact (ringChar F ≠ 2)] (ens : SoundEnsemble F PublicIO) (vm : VmTables F PublicIO)
    (ne_mem_vm_channel : ∀ table ∈ ens.ensemble.tables, vm.channel.toRaw ∉ table.circuit.channels
      := by simp [circuit_norm])
    (grts_subset_finished : ∀ table ∈ vm.tables, table.circuit.channelsWithGuarantees ⊆ vm.channel.toRaw :: ens.finished
      := by simp [circuit_norm])
    (vgrts_subset_finished : vm.verifier.channelsWithGuarantees ⊆ vm.channel.toRaw :: ens.finished
      := by simp [circuit_norm])
    (reqs_disjoint_finished : ∀ table ∈ vm.tables, ∀ channel ∈ ens.finished, channel ∉ table.circuit.channelsWithRequirements
      := by simp [circuit_norm]) :
    SoundVmEnsemble F PublicIO where
  __ := ens.ensemble.addVm vm
  soundVmChannel := ens.ensemble.addVm_soundVmChannel_of_soundChannels
    ens.soundChannels ens.finished_consistent ens.finished_subset ens.verifier_empty vm ne_mem_vm_channel
    grts_subset_finished vgrts_subset_finished reqs_disjoint_finished

namespace SoundVmEnsemble
variable {soundEns : SoundEnsemble F PublicIO} {vm : VmTables F PublicIO}
  {nmv : ∀ table ∈ soundEns.ensemble.tables, vm.channel.toRaw ∉ table.circuit.channels}
  {gsf : ∀ table ∈ vm.tables, table.circuit.channelsWithGuarantees ⊆ vm.channel.toRaw :: soundEns.finished}
  {vgsf : vm.verifier.channelsWithGuarantees ⊆ vm.channel.toRaw :: soundEns.finished}
  {rdf : ∀ table ∈ vm.tables, ∀ channel ∈ soundEns.finished, channel ∉ table.circuit.channelsWithRequirements}

@[circuit_norm] lemma addVm_spec [Fact (ringChar F ≠ 2)] (publicInput : PublicIO F) :
  (soundEns.addVm vm nmv gsf vgsf rdf).Spec publicInput =
    ∃ data, vm.verifier.Spec publicInput () (.fromInput publicInput data) := rfl
end SoundVmEnsemble
end

-- CONCRETE EXAMPLE STARTS HERE

instance (p : ℕ) [pGt : Fact (p > 512)] : Fact (ringChar (F p) ≠ 2) := .mk <| by
  simp [F, ZMod.ringChar_zmod_n]
  linarith [pGt.out]

variable {p : ℕ} [Fact p.Prime] [pGt: Fact (p > 512)]

instance (channel : StaticLookupChannel (F p) field) : NormalChannel (Channel.fromStatic _ _ channel) := by
  constructor; all_goals
  tauto

def BytesTable : StaticLookupChannel (F p) field where
  name := "bytes"
  table := List.finRange 256 |>.map ByteUtils.fromByte
  Guarantees msg := msg.val < 256
  guarantees_iff := by
    intro (msg : F p)
    simp only [List.mem_map, List.mem_finRange, true_and]
    constructor
    · intro h_lt
      exact ⟨⟨ msg.val, h_lt ⟩, ByteUtils.fromByte_eq ..⟩
    · intro ⟨ ⟨ b, hb ⟩, h_eq ⟩
      rw [← h_eq]
      apply ByteUtils.fromByte_lt

abbrev BytesChannel := Channel.fromStatic (F p) field BytesTable

-- bytes "circuit" that just pushes all bytes
-- probably shouldn't be a "circuit" at all
def pushBytes : FormalCircuitWithInteractions (F p) (fields 256) unit where
  main multiplicities := do
    let _  ← .mapFinRange 256 fun ⟨ i, _ ⟩ =>
      BytesChannel.emit multiplicities[i] (const i)

  localLength _ := 0
  localLength_eq := by simp +arith only [circuit_norm]
  output _ _ := ()

  Assumptions | multiplicities, _ => True
  Spec _ _ _ := True

  -- TODO need better tools for finite range foreach, but probably this shouldn't be a circuit anyway
  soundness := by sorry
  completeness := by sorry

  channelsWithRequirements := [ BytesChannel.toRaw ]

instance Add8Channel : Channel (F p) fieldTriple where
  name := "add8"
  Guarantees
  | mult, (x, y, z), _ =>
    mult = -1 → x.val < 256 → y.val < 256 → z.val = (x.val + y.val) % 256
  Requirements
  | mult, (x, y, z), _ =>
    mult ≠ -1 → x.val < 256 → y.val < 256 → z.val = (x.val + y.val) % 256

instance : NormalChannel (Add8Channel (p:=p)) := by constructor <;> tauto

structure Add8Inputs F where
  x : F
  y : F
  z : F
  m : F -- multiplicity
deriving ProvableStruct

def add8 : FormalCircuitWithInteractions (F p) Add8Inputs unit where
  main | { x, y, z, m } => do
    -- range-check z using the bytes channel
    -- (x and y are guaranteed to be range-checked from earlier interactions)
    BytesChannel.pull z

    -- witness the output carry
    let carry ← witness fun eval => floorDiv256 (eval (x + y))
    assertBool carry

    -- assert correctness
    x + y - z - carry * 256 === 0

    -- emit to the add8 channel with multiplicity `m`
    Add8Channel.emit m (x, y, z)

  localLength _ := 1
  output _ _ := ()

  -- TODO make coercion work without .toRaw
  channelsWithGuarantees := [ BytesChannel.toRaw ]
  channelsWithRequirements := [ Add8Channel.toRaw ]
  requirements_iff := by
    simp only [circuit_norm, seval, BytesChannel, Add8Channel]

  -- TODO feels weird to put the entire spec in the completeness assumptions
  -- can we get something from the channel interactions??
  Assumptions
  | { x, y, z, m }, _ => x.val < 256 ∧ y.val < 256 ∧ z.val < 256 ∧ z.val = (x.val + y.val) % 256
  Spec _ _ _ := True

  soundness := by
    circuit_proof_start [BytesTable, Add8Channel]
    set carry := env.get i₀
    obtain ⟨ hz, hcarry, heq ⟩ := h_holds
    intro hm hx hy
    have add_soundness := Theorems.soundness input_x input_y input_z 0 carry hx hy hz (by left; trivial) hcarry
    simp_all

  -- TODO: we didn't need to prove z < 256, but we could have
  -- for completeness, it would make sense to require proving the Guarantees as well
  -- what about the Requirements?
  completeness := by
    circuit_proof_start [BytesTable]
    set carry := env.get i₀
    rcases h_assumptions with ⟨ hx, hy, hz, heq ⟩
    have add_completeness_bool := Theorems.completeness_bool input_x input_y 0 hx hy (by simp)
    have add_completeness_add := Theorems.completeness_add input_x input_y 0 hx hy (by simp)
    simp only [add_zero] at add_completeness_bool add_completeness_add
    have h_input_z : input_z = mod256 (input_x + input_y) := by
      apply FieldUtils.ext
      rw [heq, mod256, FieldUtils.mod, FieldUtils.natToField_val, ZMod.val_add_of_lt, PNat.val_ofNat]
      linarith [hx, hy, ‹Fact (p > 512)›.elim]
    refine ⟨ hz, ?_⟩
    refine ⟨ ?_, ?_ ⟩
    · simpa [floorDiv256, h_env] using add_completeness_bool
    · simpa [h_input_z, floorDiv256, h_env] using add_completeness_add

-- define valid Fibonacci state transitions

def fibonacciStep : ℕ × ℕ → ℕ × ℕ
  | (x, y) => (y, (x + y) % 256)

def fibonacci : ℕ → (ℕ × ℕ) → (ℕ × ℕ)
  | 0, state => state
  | n + 1, state => fibonacciStep (fibonacci n state)

/-- helper lemma: fibonacci states are bytes -/
lemma fibonacci_bytes {n x y : ℕ} : (x, y) = fibonacci n (0, 1) → x < 256 ∧ y < 256 := by
  induction n generalizing x y with
  | zero => simp_all [fibonacci]
  | succ n ih =>
    specialize ih rfl
    have : 0 < 256 := by norm_num
    simp_all [fibonacci, fibonacciStep, Nat.mod_lt]

instance FibonacciChannel : Channel (F p) fieldTriple where
  name := "fibonacci"

  -- when pulling, we want the guarantee that the previous interactions pushed
  -- some tuple equal to ours which represents a valid Fibonacci step
  Guarantees
  | m, (n, x, y), _ =>
    if (m = -1)
    then
      -- (x, y) is a valid Fibonacci state
      ∃ k : ℕ, (x.val, y.val) = fibonacci k (0, 1) ∧ k % p = n.val
    else True

  Requirements
  | m, (n, x, y), _ =>
    if (m ≠ -1)
    then
      -- (x, y) is a valid Fibonacci state
      ∃ k : ℕ, (x.val, y.val) = fibonacci k (0, 1) ∧ k % p = n.val
    else True

instance : NormalChannel (FibonacciChannel (p:=p)) := by constructor <;> simp_all [FibonacciChannel]

def fib8 : FormalCircuitWithInteractions (F p) fieldTriple unit where
  main | (n, x, y) => do
    -- pull the current Fibonacci state
    FibonacciChannel.pull (n, x, y)

    -- witness the next Fibonacci value
    let z ← witness fun eval => mod256 (eval (x + y))

    -- pull from the Add8 channel to check addition
    Add8Channel.pull (x, y, z)

    -- push the next Fibonacci state
    FibonacciChannel.push (n + 1, y, z)

  localLength _ := 1
  output _ _ := ()

  channelsWithGuarantees := [ Add8Channel.toRaw, FibonacciChannel.toRaw ]
  channelsWithRequirements := [ FibonacciChannel.toRaw ]

  exposedChannels
  | (n, x, y), offset =>
    let z := var ⟨ offset ⟩
    expose FibonacciChannel [ pulled (n, x, y), pushed (n + 1, y, z) ]

  exposedChannels_eq := by
    simp only [circuit_norm, Add8Channel, FibonacciChannel]

  Assumptions
  | (n, x, y), _ =>
    ∃ k : ℕ, (x.val, y.val) = fibonacci k (0, 1) ∧ k % p = n.val
  Spec _ _ _ := True

  soundness := by
    circuit_proof_start [seval]
    rcases input with ⟨ n, x, y ⟩ -- TODO circuit_proof_start should have done this
    simp only [Prod.mk.injEq] at h_input
    simp_all only [circuit_norm]
    set z := env.get i₀
    simp only [circuit_norm, FibonacciChannel, Add8Channel, reduceIte] at h_holds ⊢
    obtain ⟨ ⟨k, fiby, hk⟩, hadd ⟩ := h_holds
    have ⟨ hx, hy ⟩ := fibonacci_bytes fiby
    use k + 1
    simp only [fibonacci, fibonacciStep, ← fiby]
    rw [ZMod.val_add, ← hk, Nat.mod_add_mod, ZMod.val_one]
    simp_all

  completeness := by
    circuit_proof_start
    rcases input with ⟨ n, x, y ⟩
    simp only [Prod.mk.injEq] at h_input
    simp_all only [circuit_norm, FibonacciChannel, Add8Channel, reduceIte]
    intro hx hy
    rw [mod256, FieldUtils.mod, FieldUtils.natToField_val, ZMod.val_add_of_lt, PNat.val_ofNat]
    linarith [hx, hy, ‹Fact (p > 512)›.elim]

-- additional circuits that pull/push remaining channel interactions
-- these really wouldn't have to be circuits, need to find a better place for tying together channels

-- completing Fibonacci channel with input and output
def fibonacciVerifier : FormalCircuitWithInteractions (F p) fieldTriple unit where
  main | (n, x, y) => do
    -- push initial state, pull the final state
    FibonacciChannel.pull (n, x, y)
    FibonacciChannel.push (0, 0, 1)

  localLength _ := 0
  output _ _ := ()

  channelsWithGuarantees := [ FibonacciChannel.toRaw ]
  channelsWithRequirements := [ ]

  requirements_iff := by
    simp only [circuit_norm, FibonacciChannel]
    intros
    exists 0
    simp [fibonacci, ZMod.val_one]

  exposedChannels
  | (n, x, y), offset =>
    expose FibonacciChannel [ pulled (n, x, y), pushed (0, 0, 1) ]

  exposedChannels_eq := by simp only [circuit_norm, FibonacciChannel]

  Assumptions
  | (n, x, y), _ =>
    ∃ k : ℕ, (x.val, y.val) = fibonacci k (0, 1) ∧ k % p = n.val
  Spec
  | (n, x, y), _, _ =>
    ∃ k : ℕ, (x.val, y.val) = fibonacci k (0, 1) ∧ k % p = n.val

  soundness := by
    circuit_proof_start
    rcases input with ⟨ n, x, y ⟩
    simp only [Prod.mk.injEq] at h_input
    simp_all only [circuit_norm, FibonacciChannel, reduceIte,
      ZMod.val_zero, ZMod.val_one]
    exact ⟨ 0, rfl, rfl ⟩

  completeness := by
    circuit_proof_start
    rcases input with ⟨ n, x, y ⟩
    simp only [Prod.mk.injEq] at h_input
    simpa [circuit_norm, FibonacciChannel, reduceIte] using h_assumptions

-- let's try to prove soundness and completeness of the Fibonacci with channels example
def fibonacciEnsemble : Ensemble (F p) fieldTriple where
  tables := [ ⟨pushBytes⟩, ⟨add8⟩, ⟨fib8⟩ ]
  channels := [ BytesChannel.toRaw, Add8Channel.toRaw, FibonacciChannel.toRaw ]
  verifier := fibonacciVerifier
  verifier_length_zero := by simp only [fibonacciVerifier, circuit_norm]
  Spec | (n, x, y) => ∃ k : ℕ, (x.val, y.val) = fibonacci k (0, 1) ∧ k % p = n.val

def fibonacciVm : VmTables (F p) fieldTriple where
  channel := FibonacciChannel
  tables := [ ⟨fib8⟩ ]
  verifier := fibonacciVerifier
  verifier_length_zero := by simp [circuit_norm, fibonacciVerifier]
  tables_channel := by simp [circuit_norm, fib8]
  verifier_channel := by simp [circuit_norm, fibonacciVerifier]

def fibonacciSoundEnsemble := SoundEnsemble.empty (F p) fieldTriple
  |>.addTable ⟨pushBytes⟩ (by simp [circuit_norm, pushBytes]) (by simp [circuit_norm, pushBytes])
  |>.addFinishedChannel BytesChannel.toRaw
  |>.addTable ⟨add8⟩ (by simp [circuit_norm, add8]) (by simp [circuit_norm, add8])
  |>.addFinishedChannel Add8Channel.toRaw
  |>.addVm fibonacciVm
    (by simp [circuit_norm, fibonacciVm, add8, pushBytes, Add8Channel, FibonacciChannel])
    (by simp [circuit_norm, fibonacciVm, fib8])
    (by simp [circuit_norm, fibonacciVm, fibonacciVerifier])
    (by simp [circuit_norm, fibonacciVm, fib8, Add8Channel, FibonacciChannel])

/--
Fibonacci soundness, concretely: if someone proves to you that constraints on this ensemble are satisfied
and that the channels are balanced, then you know that the public input is a Fibonacci number.

TODO: find a generic strategy to show that k < p, so the statement simplifies to
`(x.val, y.val) = fibonacci n.val (0, 1)`

TODO: create a nicer packaging of the hypotheses here,
e.g. VerifierAccepts could already include the constraints and balance and quantify witness existence
-/
theorem fibonacci_soundness : ∀ n x y (witness : EnsembleWitness (fibonacciSoundEnsemble (p:=p).ensemble)),
  witness.publicInput = (n, x, y) →
    witness.BalancedChannels →
    witness.Constraints →
    ∃ k : ℕ, (x.val, y.val) = fibonacci k (0, 1) ∧ k % p = n.val := by
  intro n x y witness pi_eq balance constraints
  have soundness := (fibonacciSoundEnsemble (p:=p)).soundness witness balance constraints
  simp only [circuit_norm, pi_eq, fibonacciSoundEnsemble, fibonacciVm, fibonacciVerifier] at soundness
  tauto

-- everything below is a remainder of the original AI slop proof of fibonacci soundness
-- TODO remove

/-!
## Helper lemmas for per-message channel balance
-/

/-- Sum of a list where every element is -1 equals -(length) as a field element -/
lemma sum_neg_ones {F : Type} [Ring F] (l : List F) (h : ∀ x ∈ l, x = (-1 : F)) :
    l.sum = -(l.length : F) := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.sum_cons, List.length_cons, Nat.cast_succ, neg_add_rev]
    rw [h hd (List.mem_cons.mpr (Or.inl rfl)), ih (fun x hx => h x (List.mem_cons.mpr (Or.inr hx)))]

omit [Fact (p > 512)] in
/-- In a list of interactions where all multiplicities are 1 or -1,
    if the per-message sum is 0 and (-1, msg) appears, then (1, msg) also appears.
    Requires that the characteristic is larger than the list length. -/
lemma exists_push_of_pull' {n : ℕ}
    (interactions : List (F p × Vector (F p) n)) (msg : Vector (F p) n)
    (h_mults : ∀ entry ∈ interactions, entry.2 = msg → entry.1 = 1 ∨ entry.1 = -1)
    (h_balance : ((interactions.filter (fun x => x.2 = msg)).map Prod.fst).sum = 0)
    (h_pull : (-1, msg) ∈ interactions)
    (h_bound : interactions.length < p) :
    (1, msg) ∈ interactions := by
  by_contra h_no_push
  -- Every entry for msg has mult = -1
  have h_all_neg : ∀ entry ∈ interactions, entry.2 = msg → entry.1 = -1 := by
    intro entry h_mem h_eq
    rcases h_mults entry h_mem h_eq with h | h
    · exact absurd (show (1, msg) ∈ interactions by rwa [← h_eq, ← h]) h_no_push
    · exact h
  -- The filtered list has all multiplicities = -1
  have h_neg_mults : ∀ m ∈ (interactions.filter (fun x => x.2 = msg)).map Prod.fst, m = (-1 : F p) := by
    intro m h_mem
    rw [List.mem_map] at h_mem
    obtain ⟨ ⟨ m', v ⟩, h_mem', rfl ⟩ := h_mem
    simp only [List.mem_filter, decide_eq_true_eq] at h_mem'
    exact h_all_neg _ h_mem'.1 h_mem'.2
  -- The filtered list is non-empty
  have h_nonempty : 0 < (interactions.filter (fun x => x.2 = msg)).length :=
    List.length_pos_of_mem (List.mem_filter.mpr ⟨ h_pull, by simp ⟩)
  -- The sum equals -(filtered_length : F p)
  have h_sum := sum_neg_ones _ h_neg_mults
  rw [h_balance] at h_sum
  -- So (filtered_length : F p) = 0, but 0 < filtered_length < p, contradiction
  set filtered := (interactions.filter (fun x => x.2 = msg)).map Prod.fst with h_filtered_def
  have h_len_lt_p : filtered.length < p := by
    simp only [h_filtered_def, List.length_map]
    exact lt_of_le_of_lt (List.length_filter_le _ _) h_bound
  have h_cast_zero : (filtered.length : F p) = 0 := by
    have := h_sum; -- 0 = -(filtered.length : F p)
    rw [eq_comm, neg_eq_zero] at this; exact this
  rw [ZMod.natCast_eq_zero_iff filtered.length p] at h_cast_zero
  -- p | filtered.length, but 0 < filtered.length < p, contradiction
  have h_pos : filtered.length > 0 := by
    simp only [h_filtered_def, List.length_map]; exact h_nonempty
  exact absurd (Nat.le_of_dvd h_pos h_cast_zero) (not_le.mpr h_len_lt_p)

/-- A valid Fibonacci state: (n, x, y) such that (x.val, y.val) = fibonacci k (0, 1) for some k
    with k % p = n.val -/
def IsValidFibState (n x y : F p) : Prop :=
  ∃ k : ℕ, (x.val, y.val) = fibonacci k (0, 1) ∧ k % p = n.val

omit [Fact (p > 512)] in
/-- The verifier push (0, 0, 1) is a valid fibonacci state -/
lemma verifier_push_valid : IsValidFibState (0 : F p) 0 1 :=
  ⟨ 0, by simp [fibonacci, ZMod.val_zero, ZMod.val_one], by simp ⟩

/-- From fib8 row constraints + valid input state + add8 correctness,
    the output state is also valid -/
lemma fib8_step_valid (n_i x_i y_i z_i carry : F p)
    (h_input_valid : IsValidFibState n_i x_i y_i)
    (h_carry_bool : IsBool carry)
    (h_add_eq : x_i + y_i + -z_i + -(carry * 256) = 0)
    (h_x_range : x_i.val < 256)
    (h_y_range : y_i.val < 256)
    (h_z_range : z_i.val < 256) :
    IsValidFibState (n_i + 1) y_i z_i := by
  obtain ⟨ k, h_fib, h_k ⟩ := h_input_valid
  -- from the constraints, z_i = (x_i + y_i) % 256
  have h_add := Theorems.soundness x_i y_i z_i 0 carry h_x_range h_y_range h_z_range
    (Or.inl rfl) h_carry_bool
  simp only [add_zero, ZMod.val_zero] at h_add
  have h_z_eq := (h_add h_add_eq).1
  refine ⟨ k + 1, ?_, ?_ ⟩
  · simp only [fibonacci, fibonacciStep, ← h_fib]
    simp_all
  · rw [ZMod.val_add, ← h_k, Nat.mod_add_mod, ZMod.val_one]

/-!
## Key inductive lemma: all fibonacci pushes are valid

The Fibonacci channel interactions come from:
- The verifier: push (0, 0, 1), pull (n, x, y)
- Each fib8 row: pull (n_i, x_i, y_i), push (n_i+1, y_i, z_i)

We prove by strong induction on the step counter that every push is a valid
fibonacci state. The well-foundedness relies on each fib8 row incrementing the
step counter by 1 (and p > 512 prevents wraparound for chains up to 512 steps).

**Key design principle**: The hypotheses of this lemma talk about
FibonacciChannel.Requirements (which is the OUTPUT of per-circuit soundness),
NOT about raw circuit constraints. All concrete constraint reasoning
(carry bits, addition equations, etc.) lives inside the per-circuit
soundness proofs and is not repeated here.
-/

/-- All entries pushed (mult = 1) to the fibonacci channel are valid states.

    The key hypothesis `h_fib8_soundness` captures what `fib8.soundness` gives us
    at the channel level: if a push is not the verifier push, then it came from a
    fib8 row, and IF the fib8 row's pull had a valid guarantee (the pulled state
    is a valid fibonacci state), THEN the push also satisfies its requirements
    (the pushed state is a valid fibonacci state).

    This avoids re-deriving any concrete circuit constraints — all of that is
    encapsulated inside `fib8.soundness`. -/
lemma all_fib_pushes_valid
    (fibInteractions : List (F p × Vector (F p) 3))
    -- the verifier pushes (0, 0, 1)
    -- list is shorter than the field characteristic
    (h_bound : fibInteractions.length < p)
    -- per-message balance
    (h_balance : ∀ msg : Vector (F p) 3,
      ((fibInteractions.filter (fun x => x.2 = msg)).map Prod.fst).sum = 0)
    -- all multiplicities are 1 or -1
    (h_mults : ∀ entry ∈ fibInteractions, entry.1 = 1 ∨ entry.1 = -1)
    -- For each push that is NOT the verifier push:
    -- there is a corresponding pull, and
    -- IF the pull's state is a valid fibonacci state,
    -- THEN the push's state is also a valid fibonacci state.
    -- (This is the output of fib8.soundness applied to each row.)
    (h_fib8_soundness : ∀ entry ∈ fibInteractions, entry.1 = 1 →
      -- either it's the verifier push
      entry.2 = (#v[0, 0, 1] : Vector (F p) 3) ∨
      -- or it's a fib8 push: there's a pull at step n_i, and
      -- valid input → valid output
      ∃ (n_i x_i y_i : F p),
        -- the fib8 row pulled (n_i, x_i, y_i)
        (-1, (#v[n_i, x_i, y_i] : Vector (F p) 3)) ∈ fibInteractions ∧
        -- the push's step counter is n_i + 1
        entry.2[0] = n_i + 1 ∧
        -- no wraparound
        n_i.val + 1 < p ∧
        -- if the pulled state is valid, the pushed state is valid
        -- (this is the core of fib8.soundness + add8 guarantees)
        (IsValidFibState n_i x_i y_i → IsValidFibState entry.2[0] entry.2[1] entry.2[2])) :
    -- conclusion: all pushes are valid fibonacci states
    ∀ entry ∈ fibInteractions, entry.1 = 1 →
      IsValidFibState entry.2[0] entry.2[1] entry.2[2] := by
  -- Strong induction on the step counter value
  suffices h : ∀ (n : ℕ), ∀ entry ∈ fibInteractions, entry.1 = 1 → entry.2[0].val = n →
      IsValidFibState entry.2[0] entry.2[1] entry.2[2] by
    intro entry h_mem h_push
    exact h entry.2[0].val entry h_mem h_push rfl
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro entry h_mem h_push h_step
    rcases h_fib8_soundness entry h_mem h_push with h_veq | ⟨ n_i, x_i, y_i, h_pull_mem, h_step_eq, h_no_wrap, h_valid_implies ⟩
    · -- Verifier push: entry.2 = #v[0, 0, 1]
      rw [h_veq]
      simp only [Vector.getElem_mk]
      exact verifier_push_valid
    · -- Fib8 push: valid if input is valid
      -- By per-message balance, the pull (-1, (n_i, x_i, y_i)) has a matching push
      have h_matching := exists_push_of_pull' fibInteractions (#v[n_i, x_i, y_i])
        (fun e h_mem _ => h_mults e h_mem) (h_balance _) h_pull_mem h_bound
      -- Apply IH: the matching push (1, (n_i, x_i, y_i)) is valid
      have h_input_valid : IsValidFibState n_i x_i y_i := by
        -- n_i.val < n because entry.2[0] = n_i + 1 and n = entry.2[0].val
        have : Fact (1 < p) := ⟨ by linarith [Fact.elim pGt] ⟩
        have h_lt : n_i.val < n := by
          rw [← h_step, h_step_eq, ZMod.val_add, ZMod.val_one, Nat.mod_eq_of_lt h_no_wrap]; omega
        have h_push_valid := ih n_i.val h_lt (1, #v[n_i, x_i, y_i]) h_matching rfl rfl
        simp only [Vector.getElem_mk] at h_push_valid
        exact h_push_valid
      exact h_valid_implies h_input_valid

/-!
## Structural lemmas about channel interactions

These lemmas characterize which circuits emit to which channels with what multiplicities.
They are purely mechanical - just unfolding definitions and filtering.

We state them at the level of table witness interactions, which is what the
ensemble soundness proof actually needs.
-/

omit [Fact (p > 512)] in
/-- The step counter of any valid fibonacci state is bounded by the number of interactions.

    The fibonacci sequence forms a chain: 0 → 1 → 2 → ... → n where each step
    contributes at least 2 entries to fibInteractions. Since fibInteractions.length < p,
    any step counter n_i satisfies n_i.val < p/2 < p - 1, hence n_i.val + 1 < p. -/
lemma fib_step_counter_bounded
    (fibInteractions : List (F p × Vector (F p) 3))
    (h_bound : fibInteractions.length < p)
    (h_mults : ∀ e ∈ fibInteractions, e.1 = 1 ∨ e.1 = -1)
    (h_balanced : ∀ msg, (fibInteractions.filter (·.2 = msg) |>.map (·.1)).sum = 0)
    (h_push_pred :
      ∀ entry ∈ fibInteractions, entry.1 = 1 →
        entry.2 = (#v[(0 : F p), 0, 1] : Vector (F p) 3) ∨
        ∃ (n x y : F p), ((-1 : F p), (#v[n, x, y] : Vector (F p) 3)) ∈ fibInteractions ∧
          entry.2[0] = n + 1)
    (entry : F p × Vector (F p) 3)
    (h_mem : entry ∈ fibInteractions)
    (h_push : entry.1 = 1)
    (n_i : F p)
    (h_n_eq : entry.2[0] = n_i) :
    n_i.val + 1 < p := by
  -- Prove a stronger statement by induction on Nat counters < p
  suffices h : ∀ n : ℕ, n < p →
      ∀ entry ∈ fibInteractions, entry.1 = 1 → entry.2[0] = (n : F p) → (n + 1 ≤ fibInteractions.length) by
    have h_step : entry.2[0] = (n_i.val : F p) := by
      exact h_n_eq.trans (ZMod.natCast_zmod_val n_i).symm
    have h_le := h n_i.val (ZMod.val_lt n_i) entry h_mem h_push h_step
    exact lt_of_le_of_lt h_le h_bound
  intro n h_n_lt
  suffices h : ∀ entry ∈ fibInteractions,
    entry.1 = 1 → entry.2[0] = (n : F p) → ∀ k ≤ n, ∃ entry' ∈ fibInteractions, entry'.2[0].val = k by
    intro entry h_mem h_push h_step
    -- this is should be very easy: there are n+1 distinct entries in the chain (0..n),
    -- therefore the chain length is at least n+1
    specialize h entry h_mem h_push h_step
    clear h_mem h_push h_step entry h_n_lt h_n_eq
    clear h_mem h_push entry n_i h_push_pred
    -- let's map the list to ℕ counters and use List.map_length
    -- and then talk about Finsets
    let as := fibInteractions.map (fun e => ZMod.val e.2[0])
    suffices h_natList : (∀ k ≤ n, k ∈ as) → n + 1 ≤ as.length by simp_all [as]
    intro hk
    simp only [← List.mem_toFinset] at hk
    suffices n + 1 ≤ as.toFinset.card by
      grw [List.toFinset_card_le] at this
      linarith
    generalize as.toFinset = s at *
    rw [← Finset.card_range (n + 1)]
    apply Finset.card_le_card
    intro k hk'
    simp_all only [Finset.mem_range]
    exact hk k (by linarith)

  induction n with
  | zero =>
    intro entry h_mem h_push h_step k k_le_0
    have hk : k = 0 := by linarith
    subst hk
    use entry, h_mem
    simp only [Nat.cast_zero] at h_step
    simp [h_step, ZMod.val_zero]
  | succ n ih =>
    intro entry h_mem h_push h_step k hk
    have h_pred := h_push_pred entry h_mem h_push
    rcases h_pred with h_base | ⟨n_prev, x, y, h_pull, h_step_prev⟩
    · -- base push contradicts counter n+1
      exfalso
      have h0 : entry.2[0] = 0 := by simp [h_base]
      have h_cast : ((n + 1 : ℕ) : F p) = 0 := by simpa [h_step] using h0
      have hval := ZMod.val_cast_of_lt h_n_lt
      have : (n + 1 : ℕ) = 0 := by simp [h_cast] at hval
      exact Nat.succ_ne_zero _ this
    · -- predecessor pull gives predecessor push
      have h_push_prev : (1, (#v[n_prev, x, y] : Vector (F p) 3)) ∈ fibInteractions :=
        exists_push_of_pull' fibInteractions (#v[n_prev, x, y])
          (fun e h _ => h_mults e h) (h_balanced _) h_pull h_bound
      have h_eq : n_prev = (n : F p) := by
        have h' : n_prev + 1 = (n + 1 : F p) := by simpa [h_step_prev] using h_step
        have h'' : n_prev + 1 = (n : F p) + 1 := by simpa [Nat.cast_add] using h'
        exact add_right_cancel h''
      -- if k = n+1, use current entry; otherwise use IH on predecessor
      have hk_cases : k = n + 1 ∨ k ≤ n := by
        exact Nat.lt_or_eq_of_le hk |>.elim (fun hlt => Or.inr (Nat.le_of_lt_succ hlt)) (fun heq => Or.inl heq)
      cases hk_cases with
      | inl hk_eq =>
          subst hk_eq
          use entry, h_mem
          -- counter value is n+1
          have hval := ZMod.val_cast_of_lt h_n_lt
          simpa [h_step] using hval
      | inr hk_le =>
          have h_step_prev' : (#v[n_prev, x, y] : Vector (F p) 3)[0] = (n : F p) := by
            simp [h_eq]
          have := ih (Nat.lt_of_succ_lt h_n_lt)
            (1, (#v[n_prev, x, y] : Vector (F p) 3)) h_push_prev rfl h_step_prev' k hk_le
          exact this
