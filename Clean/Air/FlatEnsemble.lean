/-
This file defines flat AIR ensembles and what soundness and completeness mean for them.
-/
module

public import Clean.Air.FlatComponent
public import Clean.Air.Balance
public import Clean.Air.Verifier

@[expose] public section

namespace Air.Flat
universe u
variable {F : Type} [FiniteField F]
variable {PublicIO : TypeMap} [ProvableType PublicIO]

/-- Channels on which a participant of an ensemble, a component or the verifier, adds guarantees and
requirements. -/
class ChannelInterface (α : Type u) (F : outParam Type) where
  channelsWithGuarantees : α → List (RawChannel F)
  channelsWithRequirements : α → List (RawChannel F)

instance : ChannelInterface (Component F) F where
  channelsWithGuarantees component := component.circuit.channelsWithGuarantees
  channelsWithRequirements component := component.circuit.channelsWithRequirements

instance : ChannelInterface (Verifier.Program F PublicIO) F where
  channelsWithGuarantees verifier := verifier.channelsWithGuarantees
  channelsWithRequirements verifier := verifier.channelsWithRequirements

namespace ChannelInterface
@[circuit_norm] lemma channelsWithGuarantees_component (component : Component F) :
    channelsWithGuarantees component = component.circuit.channelsWithGuarantees := rfl
@[circuit_norm] lemma channelsWithRequirements_component (component : Component F) :
    channelsWithRequirements component = component.circuit.channelsWithRequirements := rfl
@[circuit_norm] lemma channelsWithGuarantees_verifier (verifier : Verifier.Program F PublicIO) :
    channelsWithGuarantees verifier = verifier.channelsWithGuarantees := rfl
@[circuit_norm] lemma channelsWithRequirements_verifier (verifier : Verifier.Program F PublicIO) :
    channelsWithRequirements verifier = verifier.channelsWithRequirements := rfl
end ChannelInterface

/-- A named hint table viewing the flattened private input: `rows` rows of `width` elements,
starting at element `offset`. Elements beyond the input read as zero. -/
structure HintTable where
  key : String
  width : ℕ
  offset : ℕ
  rows : ℕ
deriving Repr, DecidableEq

/-- An ensemble of AIR components: everything a prover and a verifier implementation need. -/
structure Ensemble (F : Type) [FiniteField F] (PublicIO : TypeMap) [ProvableType PublicIO] where
  /-- Components have unique names. Their order is the order of the traces. -/
  tables : List (Component F)
  unique_names : (tables.map (·.circuit.name)).Nodup
  /-- Every channel that the components and the verifier interact with. Channels have unique
  names, so a proof system can tell them apart by name. -/
  channels : List (RawChannel F)
  unique_channel_names : (channels.map (·.name)).Nodup
  verifier : Verifier.Program F PublicIO := .empty F PublicIO
  tables_channels : ∀ table ∈ tables, table.circuit.channels ⊆ channels
  verifier_channels : verifier.channels ⊆ channels
  /-- The prover's private input to witness generation. -/
  ProverInput : TypeMap := unit
  [provableProverInput : ProvableType ProverInput]
  /-- The hint tables that witness programs read, as views of the flattened private input. -/
  hintTables : List HintTable := []

instance (ens : Ensemble F PublicIO) : ProvableType ens.ProverInput := ens.provableProverInput

/-- The public input and the component traces of an ensemble proof. -/
structure EnsembleWitness (ens : Ensemble F PublicIO) where
  tables : List (Table F)
  publicInput : PublicIO F
  same_length : ens.tables.length = tables.length
  same_circuits : ∀ i (hi : i < ens.tables.length),
    ens.tables[i] = tables[i].component
  same_data : ∀ table ∈ tables, table.data = deriveProverData tables

/-- The prover data of a witness: the input rows of its tables. -/
def EnsembleWitness.data {ens : Ensemble F PublicIO} (witness : EnsembleWitness ens) :
    ProverData F :=
  deriveProverData witness.tables

@[circuit_norm]
lemma List.flatMap_subset_iff {α β : Type*} {f : α → List β} {l₁ : List α} {l₂ : List β} :
    l₁.flatMap f ⊆ l₂ ↔ ∀ a ∈ l₁, f a ⊆ l₂ := by
  grind

namespace Ensemble
variable {ens : Ensemble F PublicIO}

def empty (F : Type) [FiniteField F] (PublicIO : TypeMap) [ProvableType PublicIO] :
  Ensemble F PublicIO where
    tables := []
    unique_names := by simp
    channels := []
    unique_channel_names := by simp
    tables_channels := by simp
    verifier_channels := by simp [circuit_norm, Verifier.Program.empty]

@[circuit_norm] lemma empty_tables :
  (empty F PublicIO).tables = [] := rfl
@[circuit_norm] lemma empty_channels :
  (empty F PublicIO).channels = [] := rfl
@[circuit_norm] lemma empty_verifier :
  (empty F PublicIO).verifier = Verifier.Program.empty F PublicIO := rfl
@[circuit_norm]
abbrev verifierOperations (ens : Ensemble F PublicIO) : Operations F :=
  ens.verifier.circuitOperations

def VerifierGuarantees (ens : Ensemble F PublicIO) (publicInput : PublicIO F) (data : ProverData F) : Prop :=
  ens.verifierOperations.FullGuarantees (.fromInput publicInput data)

@[circuit_norm]
def VerifierSpec (ens : Ensemble F PublicIO) (publicInput : PublicIO F)
    (data : ProverData F) : Prop :=
  ens.verifier.Spec publicInput data

lemma verifierSpec_of_verifierGuarantees (ens : Ensemble F PublicIO) (publicInput : PublicIO F)
    (data : ProverData F) :
    ens.VerifierGuarantees publicInput data → ens.VerifierSpec publicInput data := by
  intro guarantees
  have soundness := ens.verifier.soundness (.fromInput publicInput data) guarantees
  simpa only [VerifierSpec, ProvableType.eval_fromInput_varFromOffset_zero] using soundness

def VerifierChannelGuarantees (ens : Ensemble F PublicIO) (publicInput : PublicIO F)
    (data : ProverData F) (channel : RawChannel F) : Prop :=
  ens.verifierOperations.ChannelGuarantees channel (.fromInput publicInput data)

def VerifierChannelRequirements (ens : Ensemble F PublicIO) (publicInput : PublicIO F)
    (data : ProverData F) (channel : RawChannel F) : Prop :=
  ens.verifierOperations.ChannelRequirements channel (.fromInput publicInput data)

lemma verifierChannelRequirements_of_not_mem
    (ens : Ensemble F PublicIO) (publicInput : PublicIO F) (data : ProverData F)
    {channel : RawChannel F} :
    channel ∉ ens.verifier.channelsWithRequirements →
      ens.VerifierChannelRequirements publicInput data channel := by
  intro h_not_mem
  exact Operations.requirements_of_not_mem ens.verifierOperations
    ens.verifier.channelsWithRequirements (.fromInput publicInput data)
    (ens.verifier.operations.circuitOperations_inChannelsOrRequirementsFull _) channel h_not_mem

lemma verifierChannelGuarantees_of_not_mem
    (ens : Ensemble F PublicIO) (publicInput : PublicIO F) (data : ProverData F)
    {channel : RawChannel F} :
    channel ∉ ens.verifier.channelsWithGuarantees →
      ens.VerifierChannelGuarantees publicInput data channel := by
  intro h_not_mem
  exact Operations.guarantees_of_not_mem ens.verifierOperations
    ens.verifier.channelsWithGuarantees (.fromInput publicInput data)
    (ens.verifier.operations.circuitOperations_inChannelsOrGuaranteesFull _) channel h_not_mem

lemma verifierGuarantees_iff (ens : Ensemble F PublicIO) (publicInput : PublicIO F)
    (data : ProverData F) :
    ens.VerifierGuarantees publicInput data ↔
      ∀ channel ∈ ens.verifier.channelsWithGuarantees,
        ens.VerifierChannelGuarantees publicInput data channel :=
  Operations.guarantees_iff ens.verifierOperations ens.verifier.channelsWithGuarantees _
    (ens.verifier.operations.circuitOperations_inChannelsOrGuaranteesFull _)

def channelsWithGuarantees (ens : Ensemble F PublicIO) : List (RawChannel F) :=
  ens.verifier.channelsWithGuarantees ++
    ens.tables.flatMap (·.circuit.channelsWithGuarantees)

def channelsWithRequirements (ens : Ensemble F PublicIO) : List (RawChannel F) :=
  ens.verifier.channelsWithRequirements ++
    ens.tables.flatMap (·.circuit.channelsWithRequirements)

lemma channelsWithGuarantees_eq_verifier_append (ens : Ensemble F PublicIO) :
  ens.channelsWithGuarantees = ens.verifier.channelsWithGuarantees ++ ens.tables.flatMap (·.circuit.channelsWithGuarantees) := by
  rfl

lemma channelsWithRequirements_eq_verifier_append (ens : Ensemble F PublicIO) :
  ens.channelsWithRequirements = ens.verifier.channelsWithRequirements ++ ens.tables.flatMap (·.circuit.channelsWithRequirements) := by
  rfl

@[circuit_norm]
lemma channelsWithGuarantees_subset_iff {ens : Ensemble F PublicIO} {finished : List (RawChannel F)} :
  ens.channelsWithGuarantees ⊆ finished ↔
    ens.verifier.channelsWithGuarantees ⊆ finished ∧
      ∀ component ∈ ens.tables, component.circuit.channelsWithGuarantees ⊆ finished := by
  simp [circuit_norm, channelsWithGuarantees]
end Ensemble

namespace EnsembleWitness
variable {ens : Ensemble F PublicIO}

@[circuit_norm]
lemma tables_map_component (witness : EnsembleWitness ens) :
    witness.tables.map (·.component) = ens.tables := by
  apply List.ext_getElem
  · simp [witness.same_length]
  intro i hi hi'
  simp [witness.same_circuits i hi']

def toTables (witness : EnsembleWitness ens) : Tables F where
  tables := witness.tables
  data := witness.data
  same_data := witness.same_data

@[circuit_norm] lemma toTables_tables (witness : EnsembleWitness ens) :
  witness.toTables.tables = witness.tables := rfl
@[circuit_norm] lemma toTables_data (witness : EnsembleWitness ens) :
  witness.toTables.data = witness.data := rfl

@[circuit_norm]
lemma component_mem_tables_of_mem {witness : EnsembleWitness ens} {table : Table F} :
    table ∈ witness.tables → table.component ∈ ens.tables := by
  rw [← witness.tables_map_component]
  grind

/-- A preallocated component has exactly one row of prover data per row index. -/
lemma getRows_size_of_preallocated (witness : EnsembleWitness ens) {component : Component F}
    (hcomponent : component ∈ ens.tables)
    {mode : WitnessGeneration.PreallocatedMode F component.Input}
    (hgeneration : component.generation = .preallocated mode) :
    (witness.data.getRows component.circuit.name component.Input).size = mode.height.toNat := by
  rw [← witness.tables_map_component, List.mem_map] at hcomponent
  obtain ⟨table, htable, rfl⟩ := hcomponent
  have hmatch := table.fixed_rows_match
  simp only [Component.FixedRowsMatch, hgeneration] at hmatch
  rw [ProverData.getRows, EnsembleWitness.data, ← witness.same_data table htable,
    table.data_consistent]
  simpa using hmatch.1

@[circuit_norm]
def Constraints {ens : Ensemble F PublicIO} (witness : EnsembleWitness ens) : Prop :=
  ∀ table ∈ witness.tables, table.Constraints

@[circuit_norm]
def Assumptions {ens : Ensemble F PublicIO} (witness : EnsembleWitness ens) : Prop :=
  ∀ table ∈ witness.tables, table.Assumptions

@[circuit_norm]
def Spec {ens : Ensemble F PublicIO} (witness : EnsembleWitness ens) : Prop :=
  ens.VerifierSpec witness.publicInput witness.data ∧
    ∀ table ∈ witness.tables, table.Spec

def interactions {ens : Ensemble F PublicIO} (witness : EnsembleWitness ens) : List (Interaction F) :=
  ens.verifierOperations.interactionValues (.fromInput witness.publicInput witness.data) ++
    witness.tables.flatMap (fun table => table.interactions)

noncomputable def verifierInteractionsWith {ens : Ensemble F PublicIO}
    (witness : EnsembleWitness ens) (channel : RawChannel F) : List (Interaction F) :=
  ens.verifierOperations.interactionValuesWith channel
    (.fromInput witness.publicInput witness.data)

noncomputable def interactionsWith {ens : Ensemble F PublicIO} (witness : EnsembleWitness ens)
    (channel : RawChannel F) : List (Interaction F) :=
  witness.verifierInteractionsWith channel ++ witness.toTables.interactionsWith channel

lemma mem_interactionsWith {witness : EnsembleWitness ens}
  {channel : RawChannel F} {i : Interaction F} :
    i ∈ witness.interactionsWith channel ↔
    i ∈ witness.verifierInteractionsWith channel ∨
      ∃ table ∈ witness.tables, i ∈ table.interactionsWith channel := by
  simp only [interactionsWith, Tables.interactionsWith, toTables,
    List.mem_append, List.mem_flatMap]

lemma channel_eq_of_mem_interactionsWith {witness : EnsembleWitness ens}
  {channel : RawChannel F} {i : Interaction F} :
    i ∈ witness.interactionsWith channel → i.channel = channel := by
  rw [mem_interactionsWith]
  rintro (h_verifier | ⟨table, _, h_table⟩)
  · simp only [verifierInteractionsWith, Operations.interactionValuesWith_eq_map,
      List.mem_map] at h_verifier
    obtain ⟨interaction, h_interaction, rfl⟩ := h_verifier
    exact Operations.channel_eq_of_mem_interactionsWith h_interaction
  · exact table.channel_eq_of_mem_interactionsWith h_table

/-- Every interaction of a witness is on a channel of the ensemble. -/
lemma channel_mem_of_mem_interactions {witness : EnsembleWitness ens} {i : Interaction F} :
    i ∈ witness.interactions → i.channel ∈ ens.channels := by
  simp only [interactions, List.mem_append, List.mem_flatMap]
  rintro (h_verifier | ⟨table, h_table, h_i⟩)
  · simp only [Operations.interactionValues, List.mem_map] at h_verifier
    obtain ⟨interaction, h_interaction, rfl⟩ := h_verifier
    rw [AbstractInteraction.eval_channel]
    change interaction ∈ (ens.verifier.operations.circuitOperations).interactions at h_interaction
    rw [Verifier.Operations.circuitOperations_interactions] at h_interaction
    exact ens.verifier_channels (Verifier.Operations.channel_mem_of_mem_interactions h_interaction)
  · apply ens.tables_channels _ (component_mem_tables_of_mem h_table)
    by_contra h_not_mem
    have h_nil := table.interactionsWith_nil_of_channel_not_mem h_not_mem
    classical
    rw [Table.interactionsWith_eq_filter, List.filter_eq_nil_iff] at h_nil
    exact h_nil i h_i (by simp)

open Classical in
/-- The interactions with a channel of the ensemble are the interactions with its name, since
channel names are unique. So a proof system that balances the interactions with each channel name
balances every channel. -/
lemma interactionsWith_eq_filter_name {witness : EnsembleWitness ens} {channel : RawChannel F}
    (h_channel : channel ∈ ens.channels) :
    witness.interactionsWith channel =
      witness.interactions.filter (·.channel.name = channel.name) := by
  have h_eq : witness.interactionsWith channel =
      witness.interactions.filter (·.channel = channel) := by
    simp only [interactionsWith, verifierInteractionsWith, Tables.interactionsWith, toTables,
      interactions, List.filter_append, List.filter_flatMap,
      Operations.interactionValuesWith_eq_filter, Table.interactionsWith_eq_filter]
  rw [h_eq]
  apply List.filter_congr
  intro i h_i
  have h_mem := channel_mem_of_mem_interactions h_i
  simp only [decide_eq_decide]
  constructor
  · rintro rfl; rfl
  · intro h_name
    exact List.inj_on_of_nodup_map ens.unique_channel_names h_mem h_channel h_name

lemma verifierChannelRequirements_iff_forall {witness : EnsembleWitness ens}
    {channel : RawChannel F} :
    ens.VerifierChannelRequirements witness.publicInput witness.data channel ↔
      ∀ i ∈ witness.verifierInteractionsWith channel, i.Requirements witness.data := by
  simp only [Ensemble.VerifierChannelRequirements, Operations.ChannelRequirements,
    Operations.forall_interactionsWith_iff, verifierInteractionsWith,
    Operations.interactionValuesWith_eq_map, List.forall_mem_map]
  rfl

lemma verifierChannelGuarantees_iff_forall {witness : EnsembleWitness ens}
    {channel : RawChannel F} :
    ens.VerifierChannelGuarantees witness.publicInput witness.data channel ↔
      ∀ i ∈ witness.verifierInteractionsWith channel, i.Guarantees witness.data := by
  simp only [Ensemble.VerifierChannelGuarantees, Operations.ChannelGuarantees,
    Operations.forall_interactionsWith_iff, verifierInteractionsWith,
    Operations.interactionValuesWith_eq_map, List.forall_mem_map]
  rfl

lemma interactionsWith_of_verifier_empty {ens : Ensemble F PublicIO} {witness : EnsembleWitness ens} {channel : RawChannel F}
  (h_verifier_empty : ens.verifier = .empty F PublicIO) :
    witness.interactionsWith channel =
      witness.tables.flatMap (·.interactionsWith channel) := by
  simp [interactionsWith, verifierInteractionsWith, Tables.interactionsWith,
    circuit_norm, h_verifier_empty, Verifier.Program.empty]

/-- The ensemble interactions with a particular channel are balanced. -/
@[circuit_norm]
abbrev BalancedChannel {ens : Ensemble F PublicIO} (witness : EnsembleWitness ens)
    (channel : RawChannel F) : Prop :=
  BalancedInteractions (witness.interactionsWith channel)

/-- All ensemble interactions with all ensemble channels are balanced. -/
@[circuit_norm]
def BalancedChannels {ens : Ensemble F PublicIO} (witness : EnsembleWitness ens) : Prop :=
  ∀ channel ∈ ens.channels, BalancedChannel witness channel

/-- The interactions with every ensemble channel pass the balance check. -/
def Balanced {ens : Ensemble F PublicIO} (witness : EnsembleWitness ens) (balance : Balance F) :
    Prop :=
  ∀ channel ∈ ens.channels, balance.Balanced (witness.interactionsWith channel)

lemma balancedChannels_of_balanced {ens : Ensemble F PublicIO} {witness : EnsembleWitness ens}
    {balance : Balance F} (balanced : witness.Balanced balance) : witness.BalancedChannels :=
  fun channel h_channel =>
    balance.balancedInteractions_of_balanced _ (balanced channel h_channel)
end EnsembleWitness

/- ## Soundness, Completeness and related definitions -/

namespace Ensemble

/--
The raw "statement" that a proof about an ensemble makes, for a balance check that the proof system
performs on every channel. Could also be called "relation".

TODO: the balance checks bound the number of interactions with a channel directly, like LogUp's
bound by the characteristic. In practice, however, it's not the number of interactions that is part
of a proof, but rather the length of each individual table. It should be our verifier's job to
verify a bound on the number of interactions from the given table lengths.
-/
def Statement (ens : Ensemble F PublicIO) (balance : Balance F) (publicInput : PublicIO F) : Prop :=
  ∃ witness : EnsembleWitness ens,
    witness.publicInput = publicInput ∧
    witness.Constraints ∧ witness.Balanced balance

/-- Soundness: assumptions plus the raw statement imply the spec. -/
def Soundness (ens : Ensemble F PublicIO) (balance : Balance F)
    (Assumptions Spec : PublicIO F → Prop) : Prop :=
  ∀ publicInput, Assumptions publicInput → ens.Statement balance publicInput → Spec publicInput

/--
Completeness: assumptions plus the spec implies the raw statement.
-/
def Completeness (ens : Ensemble F PublicIO) (balance : Balance F)
    (Assumptions Spec : PublicIO F → Prop) : Prop :=
  ∀ publicInput, Assumptions publicInput → Spec publicInput → ens.Statement balance publicInput
end Ensemble

/-- An ensemble with its specification and its soundness proof under a balance check. -/
structure FormalEnsemble (F : Type) [FiniteField F]
    (PublicIO : TypeMap) [ProvableType PublicIO] (balance : Balance F) where
  ensemble : Ensemble F PublicIO
  Assumptions : PublicIO F → Prop := fun _ => True
  Spec : PublicIO F → Prop
  soundness : ensemble.Soundness balance Assumptions Spec
  /-- What the public and private inputs must satisfy for witness generation to succeed. -/
  ProverAssumptions : PublicIO F → ensemble.ProverInput F → Prop := fun _ _ => True

namespace Ensemble

/--
"Table soundness" means that we can prove the spec for each table,
assuming constraints and channel balance.
This is just Soundness, except for per-table soundness implying global soundness.
-/
@[circuit_norm]
def TableSoundness (ens : Ensemble F PublicIO) (balance : Balance F) : Prop :=
  ∀ (witness : EnsembleWitness ens),
    witness.Assumptions →
    witness.Constraints →
    witness.Balanced balance →
    witness.Spec

/-- The verifier spec and table specs imply the ensemble's public specification. -/
def SpecConsistency (ens : Ensemble F PublicIO) (Spec : PublicIO F → Prop) : Prop :=
  ∀ (witness : EnsembleWitness ens),
    -- TODO maybe we could add balanced channels + channel reqs / grts here as well, to enable you to prove
    -- something at the global level from the max interaction length, like we do below for fibonacci
    -- where we prove the counter does not overflow.
    witness.Spec →
    Spec witness.publicInput

/-- Ensemble-level assumptions imply every component's residual assumptions, for all inputs and
prover data. -/
@[circuit_norm]
def AssumptionsConsistency (ens : Ensemble F PublicIO) (Assumptions : PublicIO F → Prop) : Prop :=
  ∀ publicInput, Assumptions publicInput →
    ∀ component ∈ ens.tables, ∀ input data, component.Assumptions input data

lemma assumptions_of_assumptionsConsistency {ens : Ensemble F PublicIO}
    {Assumptions : PublicIO F → Prop}
    (consistency : ens.AssumptionsConsistency Assumptions) (witness : EnsembleWitness ens)
    (assumptions : Assumptions witness.publicInput) : witness.Assumptions := by
  intro table htable row _
  exact consistency _ assumptions _ (EnsembleWitness.component_mem_tables_of_mem htable) _ _

theorem soundness_of_tableSoundness_and_specConsistency (ens : Ensemble F PublicIO)
  (balance : Balance F) (Assumptions Spec : PublicIO F → Prop) :
  ens.TableSoundness balance →
  ens.AssumptionsConsistency Assumptions →
  ens.SpecConsistency Spec →
    ens.Soundness balance Assumptions Spec := by
  simp only [Soundness, TableSoundness, AssumptionsConsistency, SpecConsistency, Statement,
    forall_exists_index, and_imp]
  intro table_soundness assumptions_consistency spec_consistency
    publicInput assumptions witness publicInput_eq constraints balanced
  simp only [← publicInput_eq] at *
  apply spec_consistency witness
  apply table_soundness witness ?assumptions constraints balanced
  exact assumptions_of_assumptionsConsistency assumptions_consistency witness assumptions
end Ensemble

/- ## Constructing ensembles -/

namespace Ensemble
/-- Takes the verifier and the prover input from the second ensemble. -/
def merge (ens1 ens2 : Ensemble F PublicIO)
    (unique_names : ((ens2.tables ++ ens1.tables).map (·.circuit.name)).Nodup)
    (unique_channel_names : ((ens2.channels ++ ens1.channels).map (·.name)).Nodup) :
    Ensemble F PublicIO :=
  { ens2 with
    tables := ens2.tables ++ ens1.tables,
    unique_names
    channels := ens2.channels ++ ens1.channels
    unique_channel_names
    tables_channels table htable := by
      rcases List.mem_append.mp htable with htable | htable
      · exact List.Subset.trans (ens2.tables_channels table htable) (List.subset_append_left _ _)
      · exact List.Subset.trans (ens1.tables_channels table htable) (List.subset_append_right _ _)
    verifier_channels := List.Subset.trans ens2.verifier_channels (List.subset_append_left _ _) }

@[circuit_norm] lemma merge_tables (ens1 ens2 : Ensemble F PublicIO) (unique_names)
    (unique_channel_names) :
  (ens1.merge ens2 unique_names unique_channel_names).tables = ens2.tables ++ ens1.tables := rfl
@[circuit_norm] lemma merge_channels (ens1 ens2 : Ensemble F PublicIO) (unique_names)
    (unique_channel_names) :
  (ens1.merge ens2 unique_names unique_channel_names).channels = ens2.channels ++ ens1.channels :=
  rfl
@[circuit_norm] lemma merge_verifier (ens1 ens2 : Ensemble F PublicIO) (unique_names)
    (unique_channel_names) :
  (ens1.merge ens2 unique_names unique_channel_names).verifier = ens2.verifier := rfl

def addTable (ens : Ensemble F PublicIO) (table : Component F)
    (fresh : table.circuit.name ∉ ens.tables.map (·.circuit.name))
    (table_channels : table.circuit.channels ⊆ ens.channels) : Ensemble F PublicIO :=
  { ens with
    tables := table :: ens.tables
    unique_names := by simpa using List.nodup_cons.mpr ⟨fresh, ens.unique_names⟩
    tables_channels table' htable' := by
      rcases List.mem_cons.mp htable' with rfl | htable'
      · exact table_channels
      · exact ens.tables_channels table' htable' }

@[circuit_norm] lemma addTable_tables (ens : Ensemble F PublicIO) (table : Component F) (fresh)
    (table_channels) :
  (ens.addTable table fresh table_channels).tables = table :: ens.tables := rfl
@[circuit_norm] lemma addTable_channels (ens : Ensemble F PublicIO) (table : Component F) (fresh)
    (table_channels) :
  (ens.addTable table fresh table_channels).channels = ens.channels := rfl
@[circuit_norm] lemma addTable_verifier (ens : Ensemble F PublicIO) (table : Component F) (fresh)
    (table_channels) :
  (ens.addTable table fresh table_channels).verifier = ens.verifier := rfl

/-- Declare the prover's private input: its type, and the hint tables viewing it. -/
def withProverInput (ens : Ensemble F PublicIO) (ProverInput : TypeMap)
    [ProvableType ProverInput] (hintTables : List HintTable) : Ensemble F PublicIO :=
  { ens with ProverInput, provableProverInput := inferInstance, hintTables }

section
variable {ens : Ensemble F PublicIO} {ProverInput : TypeMap} [ProvableType ProverInput]
  {hintTables : List HintTable}

@[circuit_norm] lemma withProverInput_tables :
  (ens.withProverInput ProverInput hintTables).tables = ens.tables := rfl
@[circuit_norm] lemma withProverInput_channels :
  (ens.withProverInput ProverInput hintTables).channels = ens.channels := rfl
@[circuit_norm] lemma withProverInput_verifier :
  (ens.withProverInput ProverInput hintTables).verifier = ens.verifier := rfl
end

end Ensemble
end Air.Flat
