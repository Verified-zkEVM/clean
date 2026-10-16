module

public import Clean.Air.ChannelClosure
public import Clean.Circuit.InteractionRecovery

/-! # Authenticating typed records through the complete ledger

Properties of actual source records transport to matching consumers under count-bounded
balance. Dynamic source facts may depend on earlier grounding results. This interface does
not strengthen a channel's declared guarantees or assume that a received value is current. -/

@[expose] public section

namespace Air.Flat

open Circuit

variable {F : Type} [FiniteField F] {Record : TypeMap} [ProvableType Record]

/-- Every active non-pull emission has the stated typed meaning, as a consequence of raw constraints. -/
def Component.Authenticates (component : Component F) (channel : Channel F Record)
    (property : Record F → Prop) : Prop :=
  ∀ env, component.operations.ConstraintsHold env →
    ∀ interaction ∈ component.operations.interactionValuesWith channel.toRaw env,
      interaction.mult ≠ 0 → interaction.mult ≠ -1 →
        ∃ record, interaction.msg = (toElements record).toArray ∧ property record

theorem Component.Authenticates.of_pulls (component : Component F) (channel : Channel F Record)
    (property : Record F → Prop)
    (pulls : ∀ env, component.operations.ConstraintsHold env →
      ∀ interaction ∈ component.operations.interactionValuesWith channel.toRaw env,
        interaction.mult = 0 ∨ interaction.mult = -1) :
    component.Authenticates channel property := by
  intro env checked interaction member nonzero notPull
  exact ((pulls env checked interaction member).elim nonzero notPull).elim

theorem Component.Authenticates.of_silent (component : Component F) (channel : Channel F Record)
    (property : Record F → Prop) (silent : channel.toRaw ∉ component.circuit.channels) :
    component.Authenticates channel property := by
  intro env _ interaction member
  rw [Operations.interactionValuesWith, Component.interactionsWith_eq] at member
  change interaction ∈ (((component.circuit.main (varFromOffset component.Input 0)).operations
    (size component.Input)).interactionsWith channel.toRaw).map _ at member
  rw [InteractionRecovery.interactionsWith_main_eq_nil component.circuit.base _ _ _ silent] at member
  contradiction

theorem Component.Authenticates.mono {component : Component F} {channel : Channel F Record}
    {property next : Record F → Prop} (authenticated : component.Authenticates channel property)
    (implies : ∀ record, property record → next record) : component.Authenticates channel next := by
  intro env checked interaction member nonzero notPull
  obtain ⟨record, payload, valid⟩ := authenticated env checked interaction member nonzero notPull
  exact ⟨record, payload, implies record valid⟩

/-- Authentication of actual physical sources may depend on facts established elsewhere in the
ensemble, such as an earlier state or memory transition. It does not quantify over unused rows. -/
def Table.Authenticates (table : Table F) (channel : Channel F Record)
    (property : Record F → Prop) : Prop :=
  ∀ physical ∈ table.table,
    ∀ interaction ∈ table.component.operations.interactionValuesWith channel.toRaw (table.environment physical),
      interaction.mult ≠ 0 → interaction.mult ≠ -1 →
        ∃ record, interaction.msg = (toElements record).toArray ∧ property record

/-- Unconditional component-local source proofs authenticate every constrained row of a table. -/
theorem Table.Authenticates.of_component (table : Table F) (channel : Channel F Record)
    (property : Record F → Prop) (source : table.component.Authenticates channel property)
    (constraints : table.Constraints) : table.Authenticates channel property :=
  fun physical member => source (table.environment physical) (constraints physical member)

variable [DecidableEq F]

/-- A complete physical ledger transports source meaning to each unit consumer. -/
theorem authenticated_pull_of_tables (tables : List (Table F))
    (channel : Channel F Record) (property : Record F → Prop)
    (sources : ∀ table ∈ tables, table.Authenticates channel property)
    (balanced : BalancedInteractions (tables.flatMap (·.interactionsWith channel.toRaw))) (record : Record F)
    (member : channel.pulledValue record ∈ tables.flatMap (·.interactionsWith channel.toRaw)) : property record := by
  obtain ⟨provider, providerMem, samePayload, nonzero, notPull⟩ :=
    exists_push_of_pull _ balanced (channel.pulledValue record) member rfl
  obtain ⟨table, tableMem, providerMem⟩ := List.mem_flatMap.mp providerMem
  obtain ⟨physical, physicalMem, emitted⟩ := List.mem_flatMap.mp providerMem
  obtain ⟨actual, payload, valid⟩ := sources table tableMem physical physicalMem provider emitted nonzero notPull
  have equal := congrArg (fromElements (M := Record))
    (Vector.toArray_inj.mp (payload.symm.trans samePayload))
  simp only [ProvableType.fromElements_toElements] at equal
  rwa [equal] at valid

variable {Public : TypeMap} [ProvableType Public] {assembly : Ensemble F Public}

/-- Authentication uses every actual physical source and retains the original channel count bound. -/
theorem EnsembleWitness.authenticated_pull (witness : EnsembleWitness assembly)
    (channel : Channel F Record) (property : Record F → Prop)
    (sources : ∀ component ∈ assembly.allTables, component.Authenticates channel property)
    (constraints : witness.Constraints)
    (balanced : witness.BalancedChannel channel.toRaw) (record : Record F)
    (member : channel.pulledValue record ∈ witness.interactionsWith channel.toRaw) : property record :=
  authenticated_pull_of_tables witness.allTables channel property
    (fun table member => Table.Authenticates.of_component table channel property
      (sources _ (witness.mem_allTables_component_of_mem_allTables member)) (constraints table member))
    balanced record member

omit [DecidableEq F] in
private theorem guarantees_of_authenticated_pull (channel : Channel F Record)
    (interaction : Interaction F) (same : interaction.channel = channel.toRaw) (data : ProverData F)
    (authenticated : ∀ record, interaction = channel.pulledValue record → channel.Guarantees record data) :
    interaction.Guarantees data := by
  rcases interaction with ⟨raw, mult, message, width, assume⟩
  dsimp only at same
  cases same
  intro assumed pulled
  change mult = -1 at pulled
  change assume = true at assumed
  subst mult
  cases assume
  · contradiction
  · apply authenticated (fromElements (M := Record) ⟨message, width⟩)
    simp only [Channel.pulledValue, ProvableType.toElements_fromElements]

omit [DecidableEq F] in
/-- Typed pull authentication discharges the actual raw channel guarantees of every table. -/
theorem EnsembleWitness.channelGuarantees_of_authenticated_pulls (witness : EnsembleWitness assembly)
    (channel : Channel F Record)
    (authenticated : ∀ record, channel.pulledValue record ∈ witness.interactionsWith channel.toRaw →
      channel.Guarantees record witness.data) :
    ∀ table ∈ witness.allTables, table.ChannelGuarantees channel.toRaw := by
  intro table member
  rw [table.channelGuarantees_iff_forall, witness.data_eq_of_mem_allTables table member]
  intro interaction emitted
  apply guarantees_of_authenticated_pull channel interaction
    (table.channel_eq_of_mem_interactionsWith emitted) witness.data
  intro record equal
  apply authenticated record
  rw [← equal]
  exact EnsembleWitness.mem_interactionsWith.mpr ⟨table, member, emitted⟩

end Air.Flat
