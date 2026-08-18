/-
This file defines flat AIR ensembles and what soundness and completeness mean for them.
-/
import Clean.Air.Entry
import Clean.Air.Balance
import Clean.Circuit.Verifier

namespace Air.Flat
universe u
variable {F : Type} [FiniteField F]
variable {PublicIO : TypeMap} [ProvableType PublicIO]

structure ChannelInterface (F : Type) where
  channelsWithGuarantees : List (RawChannel F)
  channelsWithRequirements : List (RawChannel F)

class HasChannelInterface (F : Type) (α : Type u) where
  channelInterface : α → ChannelInterface F

def channelInterface {α : Type u} [HasChannelInterface F α] (value : α) : ChannelInterface F :=
  HasChannelInterface.channelInterface value

/-- A component exposes its circuit's channels; the window affects how often the circuit is
checked, never which channels it talks on. -/
instance : HasChannelInterface F (Component F) where
  channelInterface component :=
    { channelsWithGuarantees := component.circuit.channelsWithGuarantees
      channelsWithRequirements := component.circuit.channelsWithRequirements }

instance : HasChannelInterface F (Verifier.Program F PublicIO) where
  channelInterface verifier :=
    { channelsWithGuarantees := verifier.channelsWithGuarantees
      channelsWithRequirements := verifier.channelsWithRequirements }

@[circuit_norm] lemma component_channelInterface (component : Component F) :
    (channelInterface component).channelsWithGuarantees =
      component.circuit.channelsWithGuarantees := rfl
@[circuit_norm] lemma component_channelInterface_requirements (component : Component F) :
    (channelInterface component).channelsWithRequirements =
      component.circuit.channelsWithRequirements := rfl
@[circuit_norm] lemma verifier_channelInterface (verifier : Verifier.Program F PublicIO) :
    (channelInterface verifier).channelsWithGuarantees = verifier.channelsWithGuarantees := rfl
@[circuit_norm] lemma verifier_channelInterface_requirements
    (verifier : Verifier.Program F PublicIO) :
    (channelInterface verifier).channelsWithRequirements = verifier.channelsWithRequirements := rfl

structure Ensemble (F : Type) [FiniteField F] (PublicIO : TypeMap) [ProvableType PublicIO] where
  /-- Components form an ordered map: names are keys, while list order fixes the trace order
  consumed by witness generation and backend extraction. Each component also records, via
  `windowRows`, the shape of trace it is checked against -- which the witness is not free to
  reinterpret. -/
  tables : List (Component F)
  unique_names : (tables.map (·.circuit.name)).Nodup
  channels : List (RawChannel F)
  verifier : Verifier.Program F PublicIO := .empty F PublicIO

/-- The public input and component traces committed by an ensemble proof. -/
structure EnsembleWitness (ens : Ensemble F PublicIO) where
  tables : List (Table F)
  publicInput : PublicIO F
  same_length : ens.tables.length = tables.length
  /-- Binds the witness to the ensemble by component.

  This also pins how the trace is read: `Component.windowRows` records how many rows an
  environment spans and `window_size` ties it to the circuit's footprint, so a prover cannot
  commit a transition component as a flat trace. Under the older `Entry`/`TableKind` design that
  had to be bound separately, because both readings imposed the same width obligation. -/
  same_circuits : ∀ i (hi : i < ens.tables.length),
    ens.tables[i] = tables[i].component

/-- External prover data consists of the complete inputs of the committed component traces. -/
def EnsembleWitness.data {ens : Ensemble F PublicIO} (witness : EnsembleWitness ens) :
    ProverData F :=
  Table.deriveProverData witness.tables

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

lemma verifierSoundness (ens : Ensemble F PublicIO) (publicInput : PublicIO F)
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
    (ens.verifier.operations.inChannelsOrRequirementsFull _) channel h_not_mem

lemma verifierChannelGuarantees_of_not_mem
    (ens : Ensemble F PublicIO) (publicInput : PublicIO F) (data : ProverData F)
    {channel : RawChannel F} :
    channel ∉ ens.verifier.channelsWithGuarantees →
      ens.VerifierChannelGuarantees publicInput data channel := by
  intro h_not_mem
  exact Operations.guarantees_of_not_mem ens.verifierOperations
    ens.verifier.channelsWithGuarantees (.fromInput publicInput data)
    (ens.verifier.operations.inChannelsOrGuaranteesFull _) channel h_not_mem

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

/-- The witness's traces fill exactly the ensemble's components. -/
@[circuit_norm]
lemma tables_map_component (witness : EnsembleWitness ens) :
    witness.tables.map (·.component) = ens.tables := by
  apply List.ext_getElem
  · simp [witness.same_length]
  intro i hi hi'
  simp [witness.same_circuits i hi']

private lemma tableNamesNodup (witness : EnsembleWitness ens) :
    (witness.tables.map (fun table => table.component.circuit.name)).Nodup := by
  rw [show witness.tables.map (fun table => table.component.circuit.name) =
    ens.tables.map (·.circuit.name) by
      calc
        _ = (witness.tables.map (·.component)).map (·.circuit.name) := by simp
        _ = ens.tables.map (·.circuit.name) :=
          congrArg (List.map (·.circuit.name)) witness.tables_map_component]
  exact ens.unique_names

lemma data_consistent (witness : EnsembleWitness ens) :
    ∀ table ∈ witness.tables, table.DataConsistency witness.data := by
  intro table htable
  rw [Table.dataConsistency_iff]
  exact Table.deriveProverData_eq_of_mem witness.tables witness.tableNamesNodup
    htable _

def tableContext (witness : EnsembleWitness ens) : TableContext F where
  tables := witness.tables
  data := witness.data
  data_consistent := witness.data_consistent

@[circuit_norm] lemma tableContext_tables (witness : EnsembleWitness ens) :
  witness.tableContext.tables = witness.tables := rfl
@[circuit_norm] lemma tableContext_data (witness : EnsembleWitness ens) :
  witness.tableContext.data = witness.data := rfl

@[circuit_norm]
lemma mem_component_of_mem {witness : EnsembleWitness ens} {table : Table F} :
    table ∈ witness.tables → table.component ∈ ens.tables := by
  rw [← witness.tables_map_component]
  grind

def Constraints {ens : Ensemble F PublicIO} (witness : EnsembleWitness ens) : Prop :=
  witness.tableContext.Constraints

def Assumptions {ens : Ensemble F PublicIO} (witness : EnsembleWitness ens) : Prop :=
  witness.tableContext.Assumptions

def Spec {ens : Ensemble F PublicIO} (witness : EnsembleWitness ens) : Prop :=
  ens.VerifierSpec witness.publicInput witness.data ∧
    ∀ table ∈ witness.tables, table.Spec witness.data

def interactions {ens : Ensemble F PublicIO} (witness : EnsembleWitness ens) : List (Interaction F) :=
  ens.verifierOperations.interactionValues (.fromInput witness.publicInput witness.data) ++
    witness.tables.flatMap (fun table => table.interactions witness.data)

noncomputable def verifierInteractionsWith {ens : Ensemble F PublicIO}
    (witness : EnsembleWitness ens) (channel : RawChannel F) : List (Interaction F) :=
  ens.verifierOperations.interactionValuesWith channel
    (.fromInput witness.publicInput witness.data)

noncomputable def interactionsWith {ens : Ensemble F PublicIO} (witness : EnsembleWitness ens)
    (channel : RawChannel F) : List (Interaction F) :=
  witness.verifierInteractionsWith channel ++ witness.tableContext.interactionsWith channel

@[circuit_norm] lemma constraints_iff {ens : Ensemble F PublicIO}
    (witness : EnsembleWitness ens) :
  witness.Constraints ↔
    ∀ table ∈ witness.tables, table.Constraints witness.data := by
  rfl

@[circuit_norm] lemma assumptions_iff {ens : Ensemble F PublicIO}
    (witness : EnsembleWitness ens) :
  witness.Assumptions ↔
    ∀ table ∈ witness.tables, table.Assumptions witness.data := by
  rfl

@[circuit_norm] lemma spec_iff {ens : Ensemble F PublicIO}
    (witness : EnsembleWitness ens) :
  witness.Spec ↔ ens.VerifierSpec witness.publicInput witness.data ∧
    ∀ table ∈ witness.tables, table.Spec witness.data := by
  rfl

lemma mem_interactionsWith {witness : EnsembleWitness ens}
  {channel : RawChannel F} {i : Interaction F} :
    i ∈ witness.interactionsWith channel ↔
    i ∈ witness.verifierInteractionsWith channel ∨
      ∃ table ∈ witness.tables, i ∈ table.interactionsWith witness.data channel := by
  simp only [interactionsWith, TableContext.interactionsWith, tableContext,
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
  · exact RowEnvs.channel_eq_of_mem_interactionsWith (table:=table) h_table

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
      witness.tables.flatMap (·.interactionsWith witness.data channel) := by
  simp [interactionsWith, verifierInteractionsWith, TableContext.interactionsWith,
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
end EnsembleWitness

/- ## Soundness, Completeness and related definitions -/

namespace Ensemble

/--
The raw "statement" that a proof about an ensemble makes. Could also be called "relation".

TODO: we currently assume a proof system that already provides us with the fact that the
total interaction length doesn't overflow (as part of `BalancedChannels`).

In practice, however, it's not the total interaction length that is part of a proof,
but rather the length of each individual table. It should be our verifier's job to
verify a bound on the interaction length from the given table lengths.
-/
def Statement (ens : Ensemble F PublicIO) (publicInput : PublicIO F) : Prop :=
  ∃ witness : EnsembleWitness ens,
    witness.publicInput = publicInput ∧
    witness.Constraints ∧ witness.BalancedChannels

/-- Soundness: assumptions plus the raw statement imply the spec. -/
def Soundness (ens : Ensemble F PublicIO) (Assumptions Spec : PublicIO F → Prop) : Prop :=
  ∀ publicInput, Assumptions publicInput → ens.Statement publicInput → Spec publicInput

/--
Completeness: assumptions plus the spec implies the raw statement.
-/
def Completeness (ens : Ensemble F PublicIO) (Assumptions Spec : PublicIO F → Prop) : Prop :=
  ∀ publicInput, Assumptions publicInput → Spec publicInput → ens.Statement publicInput
end Ensemble

structure FormalEnsemble (F : Type) [FiniteField F]
    (PublicIO : TypeMap) [ProvableType PublicIO] where
  ensemble : Ensemble F PublicIO
  Assumptions : PublicIO F → Prop := fun _ => True
  Spec : PublicIO F → Prop
  soundness : ensemble.Soundness Assumptions Spec
  -- completeness : ensemble.Completeness Assumptions Spec

namespace Ensemble

/--
"Table soundness" means that we can prove the spec for each table,
assuming constraints and channel balance.
This is just Soundness, except for per-table soundness implying global soundness.
-/
@[circuit_norm]
def TableSoundness (ens : Ensemble F PublicIO) : Prop :=
  ∀ (witness : EnsembleWitness ens),
    witness.Assumptions →
    witness.Constraints →
    witness.BalancedChannels →
    witness.Spec

/-- The verifier spec and table specs imply the ensemble's public specification. -/
def SpecConsistency (ens : Ensemble F PublicIO) (Spec : PublicIO F → Prop) : Prop :=
  ∀ (witness : EnsembleWitness ens),
    -- TODO maybe we could add balanced channels + channel reqs / grts here as well, to enable you to prove
    -- something at the global level from the max interaction length, like we do below for fibonacci
    -- where we prove the counter does not overflow.
    witness.Spec →
    Spec witness.publicInput

/-- Ensemble-level assumptions imply every table's assumptions. -/
def AssumptionsConsistency (ens : Ensemble F PublicIO) (Assumptions : PublicIO F → Prop) : Prop :=
  ∀ (witness : EnsembleWitness ens),
    Assumptions witness.publicInput →
    witness.Assumptions

theorem soundness_of_tableSoundness_and_specConsistency (ens : Ensemble F PublicIO)
  (Assumptions Spec : PublicIO F → Prop) :
  ens.TableSoundness →
  ens.AssumptionsConsistency Assumptions →
  ens.SpecConsistency Spec →
    ens.Soundness Assumptions Spec := by
  simp only [Soundness, TableSoundness, AssumptionsConsistency, SpecConsistency, Statement,
    forall_exists_index, and_imp]
  intro table_soundness assumptions_consistency spec_consistency
    publicInput assumptions witness publicInput_eq constraints balance
  simp only [← publicInput_eq] at *
  apply spec_consistency witness
  apply table_soundness witness ?assumptions constraints balance
  exact assumptions_consistency witness assumptions
end Ensemble

/- ## Constructing ensembles -/

namespace Ensemble
/-- Takes the verifier from the second ensemble. -/
def merge (ens1 ens2 : Ensemble F PublicIO)
    (unique_names : ((ens2.tables ++ ens1.tables).map (·.circuit.name)).Nodup) :
    Ensemble F PublicIO :=
  { ens2 with
    tables := ens2.tables ++ ens1.tables,
    unique_names
    channels := ens2.channels ++ ens1.channels }

@[circuit_norm] lemma merge_tables (ens1 ens2 : Ensemble F PublicIO) (unique_names) :
  (ens1.merge ens2 unique_names).tables = ens2.tables ++ ens1.tables := rfl
@[circuit_norm] lemma merge_verifier (ens1 ens2 : Ensemble F PublicIO) (unique_names) :
  (ens1.merge ens2 unique_names).verifier = ens2.verifier := rfl

/--
Add a component to the ensemble.

There is no separate `addTransitionTable`: how often the circuit is checked, and against how many
rows, is read off `table.windowRows`, so a transition component is added exactly like a flat one.
Note an `n`-row transition trace imposes `n - 1` constraint instances and a trace of fewer than
`windowRows` rows is unconstrained -- so boundary conditions must be pinned through channel
interactions.
-/
def addTable (ens : Ensemble F PublicIO) (table : Component F)
    (fresh : table.circuit.name ∉ ens.tables.map (·.circuit.name)) : Ensemble F PublicIO :=
  { ens with
    tables := table :: ens.tables
    unique_names := by simpa using List.nodup_cons.mpr ⟨fresh, ens.unique_names⟩ }

@[circuit_norm] lemma addTable_tables (ens : Ensemble F PublicIO) (table : Component F) (fresh) :
  (ens.addTable table fresh).tables = table :: ens.tables := rfl
@[circuit_norm] lemma addTable_verifier (ens : Ensemble F PublicIO) (table : Component F) (fresh) :
  (ens.addTable table fresh).verifier = ens.verifier := rfl

end Ensemble
end Air.Flat
