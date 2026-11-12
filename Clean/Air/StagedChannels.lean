module

public import Clean.Air.FlatEnsemble

@[expose] public section

/-!
# Soundness by channel finishing order

`OrderedChannel` orders tables: a table may not both pull from a channel and owe requirements on it.
That rules out a table whose requirements on a channel follow from guarantees on *other* channels,
like a pull whose multiplicity is range-checked by a lookup on another channel: `LT` pulls `IS_HALF`
with multiplicity `μ`, and `μ ≤ 255` comes from pulling `ARE_BYTES[μ, 0]`.

Here channels are ordered instead. `finished` lists the channels newest first, and a component's
requirements on a channel may use its guarantees on the channels finished before it
(`Component.StagedRequirements`). Then, by induction from the oldest channel, every channel's
requirements hold, so by consistency every channel's guarantees hold, and every table's spec follows.
-/

variable {F : Type} [FiniteField F]

namespace Air.Flat

/-- The requirements of `table` on `channel` follow from its assumptions, its constraints and its
guarantees on `earlier` channels. -/
def Table.RequirementsAfter (table : Table F) (channel : RawChannel F)
    (earlier : List (RawChannel F)) : Prop :=
  table.Assumptions → table.Constraints → (∀ c ∈ earlier, table.ChannelGuarantees c) →
    table.ChannelRequirements channel

/-- `Table.RequirementsAfter` for every table of the component. -/
def Component.RequirementsAfter (component : Component F) (channel : RawChannel F)
    (earlier : List (RawChannel F)) : Prop :=
  ∀ table : Table F, table.component = component → table.RequirementsAfter channel earlier

/-- The requirements of a component on each channel of `finished`, newest first, follow from its
guarantees on the channels finished before it. -/
def Component.StagedRequirements (component : Component F) : List (RawChannel F) → Prop
  | [] => True
  | channel :: earlier =>
    component.RequirementsAfter channel earlier ∧ component.StagedRequirements earlier

@[circuit_norm] lemma Component.stagedRequirements_nil (component : Component F) :
    component.StagedRequirements [] := trivial

@[circuit_norm] lemma Component.stagedRequirements_cons (component : Component F)
    (channel : RawChannel F) (earlier : List (RawChannel F)) :
    component.StagedRequirements (channel :: earlier) ↔
      component.RequirementsAfter channel earlier ∧ component.StagedRequirements earlier :=
  .rfl

/-- A component owes nothing on a channel it doesn't require. -/
lemma Component.requirementsAfter_of_not_mem {component : Component F} {channel : RawChannel F}
    (earlier : List (RawChannel F))
    (h : channel ∉ component.circuit.channelsWithRequirements) :
    component.RequirementsAfter channel earlier := by
  rintro table rfl - constraints -
  exact table.requirements_of_not_mem_of_constraints constraints h

/-- A component whose guarantees all come from earlier channels gets its requirements from
soundness. -/
lemma Component.requirementsAfter_of_guarantees_subset {component : Component F}
    {channel : RawChannel F} {earlier : List (RawChannel F)}
    (h : component.circuit.channelsWithGuarantees ⊆ earlier) :
    component.RequirementsAfter channel earlier := by
  rintro table rfl assumptions constraints guarantees
  have all_guarantees : table.Guarantees := by
    rw [Table.guarantees_iff_channelGuarantees]
    exact fun c hc => guarantees c (h hc)
  exact table.channelRequirements_of_requirements
    (Table.weakSoundness assumptions constraints all_guarantees).2

/-- Staged requirements on a list of channels, from one of the two lemmas above for each channel. -/
lemma Component.stagedRequirements_of_forall {component : Component F} :
    ∀ {finished : List (RawChannel F)},
    (∀ (channel : RawChannel F) (earlier : List (RawChannel F)),
      (∃ later, later ++ channel :: earlier = finished) →
      component.RequirementsAfter channel earlier) →
    component.StagedRequirements finished
  | [], _ => trivial
  | channel :: earlier, h =>
    ⟨h channel earlier ⟨[], rfl⟩,
      Component.stagedRequirements_of_forall fun c e ⟨later, hl⟩ =>
        h c e ⟨channel :: later, by simp [hl]⟩⟩

namespace Ensemble
variable {PublicIO : TypeMap} [ProvableType PublicIO]

/-- Every table's guarantees on every channel of `finished` hold, by induction from the oldest
channel. -/
theorem channelGuarantees_of_staged {ens : Ensemble F PublicIO} {N : ℕ}
    (verifier_empty : ens.verifier = .empty F PublicIO)
    (witness : EnsembleWitness ens) (assumptions : witness.Assumptions)
    (constraints : witness.Constraints)
    (balanced : ∀ channel ∈ ens.channels, BalancedUpTo N (witness.interactionsWith channel)) :
    ∀ {finished : List (RawChannel F)}, finished ⊆ ens.channels →
    (∀ channel ∈ finished, channel.ConsistentUpTo N) →
    (∀ component ∈ ens.tables, component.StagedRequirements finished) →
    ∀ table ∈ witness.tables, ∀ channel ∈ finished, table.ChannelGuarantees channel
  | [], _, _, _ => by simp
  | channel :: earlier, finished_subset, consistent, staged => by
    have ih := channelGuarantees_of_staged verifier_empty witness assumptions constraints balanced
      (List.subset_of_cons_subset finished_subset)
      (fun c hc => consistent c (List.mem_cons_of_mem _ hc))
      (fun component h => (staged component h).2)
    -- the requirements of every table on `channel` hold, given the guarantees on earlier channels
    have requirements : ∀ table ∈ witness.tables, table.ChannelRequirements channel :=
      fun table h_table =>
        (staged table.component (witness.component_mem_tables_of_mem h_table)).1 table rfl
          (assumptions table h_table) (constraints table h_table) (ih table h_table)
    -- so all interactions with `channel` satisfy their requirements, and by consistency their
    -- guarantees
    have : channel.ConsistentUpTo N := consistent channel List.mem_cons_self
    have all_guarantees := RawChannel.ConsistentUpTo.consistent
      (witness.interactionsWith channel) witness.data
      (balanced channel (finished_subset List.mem_cons_self)) (by
        intro i h_i
        refine ⟨witness.channel_eq_of_mem_interactionsWith h_i, ?_⟩
        rw [EnsembleWitness.interactionsWith_of_verifier_empty verifier_empty, List.mem_flatMap]
          at h_i
        obtain ⟨table, h_table, h_i⟩ := h_i
        have := (requirements table h_table)
        rw [Table.channelRequirements_iff_forall, witness.same_data table h_table] at this
        exact this i h_i)
    intro table h_table c h_c
    rcases List.mem_cons.mp h_c with rfl | h_c
    · rw [Table.channelGuarantees_iff_forall, witness.same_data table h_table]
      intro i h_i
      apply all_guarantees i
      rw [EnsembleWitness.interactionsWith_of_verifier_empty verifier_empty, List.mem_flatMap]
      exact ⟨table, h_table, h_i⟩
    · exact ih table h_table c h_c

/--
Soundness from channel finishing order: if every table's guarantees come from finished channels,
every finished channel is consistent under the balance check, and every component's requirements
on a finished channel follow from its guarantees on the channels finished before it, then the
tables are sound.
-/
theorem tableSoundness_of_staged {ens : Ensemble F PublicIO} {balance : Balance F}
    (finished : List (RawChannel F))
    (verifier_empty : ens.verifier = .empty F PublicIO)
    (finished_subset : finished ⊆ ens.channels)
    (subset_finished : ∀ component ∈ ens.tables,
      component.circuit.channelsWithGuarantees ⊆ finished)
    (consistent : ∀ channel ∈ finished, channel.ConsistentUpTo balance.pullBound)
    (staged : ∀ component ∈ ens.tables, component.StagedRequirements finished) :
    ens.TableSoundness balance := by
  intro witness assumptions constraints fit balanced
  have guarantees := channelGuarantees_of_staged verifier_empty witness assumptions constraints
    (witness.balancedChannels_of_balanced fit balanced)
    finished_subset consistent staged
  refine ⟨?_, fun table h_table => ?_⟩
  · apply ens.verifierSpec_of_verifierGuarantees
    rw [verifierGuarantees_iff]
    intro channel h_channel
    simp [verifier_empty, Verifier.Program.empty, circuit_norm] at h_channel
  · have all_guarantees : table.Guarantees := by
      rw [Table.guarantees_iff_channelGuarantees]
      exact fun c hc => guarantees table h_table c
        (subset_finished table.component (witness.component_mem_tables_of_mem h_table) hc)
    exact (Table.weakSoundness (assumptions table h_table) (constraints table h_table)
      all_guarantees).1

end Ensemble

/-!
## Stages: a channel and a class of its messages

A channel that one table both pulls from and pushes to, on different messages, is not a cycle. The
ALU bus of a VM is the example: a division table pulls `LT` and `MUL` results and pushes `DIVREM`
results, all on the same bus. Ordering by stage, a channel together with a class of messages,
lets the `DIVREM` stage be finished after the `LT`/`MUL` stage. Balance is message by message
(`BalancedUpTo.filter_msg`), so each stage balances by itself. A whole channel is the stage whose
class is every message.
-/

/-- The messages of one class on one channel. -/
structure Stage (F : Type) [FiniteField F] where
  channel : RawChannel F
  cls : Array F → Bool := fun _ => true

/-- The guarantees of `table` on the interactions of a stage. -/
def Table.GuaranteesOn (table : Table F) (stage : Stage F) : Prop :=
  ∀ i ∈ table.interactionsWith stage.channel, stage.cls i.msg → i.Guarantees table.data

/-- The requirements of `table` on the interactions of a stage. -/
def Table.RequirementsOn (table : Table F) (stage : Stage F) : Prop :=
  ∀ i ∈ table.interactionsWith stage.channel, stage.cls i.msg → i.Requirements table.data

/-- The requirements of `table` on a stage follow from its guarantees on `earlier` stages. -/
def Table.RequirementsAfterOn (table : Table F) (stage : Stage F) (earlier : List (Stage F)) :
    Prop :=
  table.Assumptions → table.Constraints → (∀ s ∈ earlier, table.GuaranteesOn s) →
    table.RequirementsOn stage

def Component.RequirementsAfterOn (component : Component F) (stage : Stage F)
    (earlier : List (Stage F)) : Prop :=
  ∀ table : Table F, table.component = component → table.RequirementsAfterOn stage earlier

/-- `Component.StagedRequirements` over stages, newest first. -/
def Component.StagedRequirementsOn (component : Component F) : List (Stage F) → Prop
  | [] => True
  | stage :: earlier =>
    component.RequirementsAfterOn stage earlier ∧ component.StagedRequirementsOn earlier

@[circuit_norm] lemma Component.stagedRequirementsOn_nil (component : Component F) :
    component.StagedRequirementsOn [] := trivial

@[circuit_norm] lemma Component.stagedRequirementsOn_cons (component : Component F)
    (stage : Stage F) (earlier : List (Stage F)) :
    component.StagedRequirementsOn (stage :: earlier) ↔
      component.RequirementsAfterOn stage earlier ∧ component.StagedRequirementsOn earlier :=
  .rfl

/-- Guarantees on stages that cover every pull of a table give all its guarantees. -/
lemma Table.guarantees_of_guaranteesOn {table : Table F} {stages : List (Stage F)}
    (covered : ∀ c ∈ table.component.circuit.channelsWithGuarantees,
      ∀ i ∈ table.interactionsWith c, i.direction = .pull →
        ∃ s ∈ stages, s.channel = c ∧ s.cls i.msg)
    (guarantees : ∀ s ∈ stages, table.GuaranteesOn s) : table.Guarantees := by
  rw [Table.guarantees_iff_channelGuarantees]
  intro c h_c
  rw [Table.channelGuarantees_iff_forall]
  intro i h_i
  by_cases h_pull : i.direction = .pull
  · obtain ⟨ s, h_s, rfl, h_cls ⟩ := covered c h_c i h_i h_pull
    exact guarantees s h_s i h_i h_cls
  · exact fun h => absurd h h_pull

/-- A component owes nothing on a stage of a channel it doesn't require. -/
lemma Component.requirementsAfterOn_of_not_mem {component : Component F} {stage : Stage F}
    (earlier : List (Stage F))
    (h : stage.channel ∉ component.circuit.channelsWithRequirements) :
    component.RequirementsAfterOn stage earlier := by
  rintro table rfl - constraints - i h_i -
  have := table.requirements_of_not_mem_of_constraints constraints h
  rw [Table.channelRequirements_iff_forall] at this
  exact this i h_i

/-- A component whose pulls all lie in earlier stages gets its requirements from soundness. -/
lemma Component.requirementsAfterOn_of_covered {component : Component F} {stage : Stage F}
    {earlier : List (Stage F)}
    (covered : ∀ table : Table F, table.component = component →
      ∀ c ∈ component.circuit.channelsWithGuarantees,
      ∀ i ∈ table.interactionsWith c, i.direction = .pull →
        ∃ s ∈ earlier, s.channel = c ∧ s.cls i.msg) :
    component.RequirementsAfterOn stage earlier := by
  rintro table rfl assumptions constraints guarantees i h_i -
  have all_guarantees := Table.guarantees_of_guaranteesOn (covered table rfl) guarantees
  have := table.channelRequirements_of_requirements (channel := stage.channel)
    (Table.weakSoundness assumptions constraints all_guarantees).2
  rw [Table.channelRequirements_iff_forall] at this
  exact this i h_i

/-- The same, when every message of each guarantee channel lies in an earlier stage. -/
lemma Component.requirementsAfterOn_of_guarantees_subset {component : Component F}
    {stage : Stage F} {earlier : List (Stage F)}
    (h : ∀ c ∈ component.circuit.channelsWithGuarantees, ∀ msg,
      ∃ s ∈ earlier, s.channel = c ∧ s.cls msg) :
    component.RequirementsAfterOn stage earlier :=
  Component.requirementsAfterOn_of_covered fun _ _ c h_c i _ _ => h c h_c i.msg

/-- A channel-level `RequirementsAfter` gives the stage-level one for the whole channel, when every
earlier channel is a whole-channel stage. -/
lemma Component.requirementsAfterOn_of_requirementsAfter {component : Component F}
    {channel : RawChannel F} {earlierChannels : List (RawChannel F)} {earlier : List (Stage F)}
    (h : component.RequirementsAfter channel earlierChannels)
    (h_earlier : ∀ c ∈ earlierChannels, ∃ s ∈ earlier, s.channel = c ∧ ∀ msg, s.cls msg) :
    component.RequirementsAfterOn { channel } earlier := by
  rintro table h_comp assumptions constraints guarantees i h_i -
  have := h table h_comp assumptions constraints (fun c hc => by
    obtain ⟨s, hs, rfl, hall⟩ := h_earlier c hc
    rw [Table.channelGuarantees_iff_forall]
    exact fun i hi => guarantees s hs i hi (hall _))
  rw [Table.channelRequirements_iff_forall] at this
  exact this i h_i

namespace Ensemble
variable {PublicIO : TypeMap} [ProvableType PublicIO]

/-- Every table's guarantees on every stage hold, by induction from the oldest stage. -/
theorem guaranteesOn_of_stagedOn {ens : Ensemble F PublicIO} {N : ℕ}
    (verifier_empty : ens.verifier = .empty F PublicIO)
    (witness : EnsembleWitness ens) (assumptions : witness.Assumptions)
    (constraints : witness.Constraints)
    (balanced : ∀ channel ∈ ens.channels, BalancedUpTo N (witness.interactionsWith channel)) :
    ∀ {finished : List (Stage F)}, (∀ s ∈ finished, s.channel ∈ ens.channels) →
    (∀ s ∈ finished, s.channel.ConsistentUpTo N) →
    (∀ component ∈ ens.tables, component.StagedRequirementsOn finished) →
    ∀ table ∈ witness.tables, ∀ s ∈ finished, table.GuaranteesOn s
  | [], _, _, _ => by simp
  | stage :: earlier, finished_channels, consistent, staged => by
    have ih := guaranteesOn_of_stagedOn verifier_empty witness assumptions constraints balanced
      (fun s hs => finished_channels s (List.mem_cons_of_mem _ hs))
      (fun s hs => consistent s (List.mem_cons_of_mem _ hs))
      (fun component h => (staged component h).2)
    have requirements : ∀ table ∈ witness.tables, table.RequirementsOn stage :=
      fun table h_table =>
        (staged table.component (witness.component_mem_tables_of_mem h_table)).1 table rfl
          (assumptions table h_table) (constraints table h_table) (ih table h_table)
    -- the stage's interactions balance by themselves, satisfy their requirements, and so by
    -- consistency their guarantees
    have : stage.channel.ConsistentUpTo N := consistent stage List.mem_cons_self
    have mem_stage : ∀ i, i ∈ (witness.interactionsWith stage.channel).filter
        (fun i => stage.cls i.msg) ↔ (∃ table ∈ witness.tables,
          i ∈ table.interactionsWith stage.channel) ∧ stage.cls i.msg = true := by
      intro i
      rw [List.mem_filter, EnsembleWitness.interactionsWith_of_verifier_empty verifier_empty,
        List.mem_flatMap]
    have all_guarantees := RawChannel.ConsistentUpTo.consistent
      ((witness.interactionsWith stage.channel).filter fun i => stage.cls i.msg) witness.data
      ((balanced stage.channel (finished_channels stage List.mem_cons_self)).filter_msg _)
      (by
        intro i h_i
        refine ⟨witness.channel_eq_of_mem_interactionsWith (List.mem_filter.mp h_i).1, ?_⟩
        obtain ⟨⟨table, h_table, h_i⟩, h_cls⟩ := (mem_stage i).mp h_i
        have := requirements table h_table i h_i h_cls
        rwa [witness.same_data table h_table] at this)
    intro table h_table s h_s
    rcases List.mem_cons.mp h_s with rfl | h_s
    · intro i h_i h_cls
      rw [witness.same_data table h_table]
      exact all_guarantees i ((mem_stage i).mpr ⟨⟨table, h_table, h_i⟩, h_cls⟩)
    · exact ih table h_table s h_s

/--
Soundness from the finishing order of stages. Every pull of every table lies in a finished stage;
every finished stage's channel is consistent under the balance check; every component's
requirements on a stage follow from its guarantees on the stages finished before it.
-/
theorem tableSoundness_of_stagedOn {ens : Ensemble F PublicIO} {balance : Balance F}
    (finished : List (Stage F))
    (verifier_empty : ens.verifier = .empty F PublicIO)
    (finished_channels : ∀ s ∈ finished, s.channel ∈ ens.channels)
    (covered : ∀ component ∈ ens.tables, ∀ c ∈ component.circuit.channelsWithGuarantees,
      ∀ msg, ∃ s ∈ finished, s.channel = c ∧ s.cls msg)
    (consistent : ∀ s ∈ finished, s.channel.ConsistentUpTo balance.pullBound)
    (staged : ∀ component ∈ ens.tables, component.StagedRequirementsOn finished) :
    ens.TableSoundness balance := by
  intro witness assumptions constraints fit balanced
  have guarantees := guaranteesOn_of_stagedOn verifier_empty witness assumptions constraints
    (witness.balancedChannels_of_balanced fit balanced)
    finished_channels consistent staged
  refine ⟨?_, fun table h_table => ?_⟩
  · apply ens.verifierSpec_of_verifierGuarantees
    rw [verifierGuarantees_iff]
    intro channel h_channel
    simp [verifier_empty, Verifier.Program.empty, circuit_norm] at h_channel
  · have h_comp := witness.component_mem_tables_of_mem h_table
    have all_guarantees : table.Guarantees :=
      Table.guarantees_of_guaranteesOn
        (fun c h_c i _ _ => covered table.component h_comp c h_c i.msg)
        (guarantees table h_table)
    exact (Table.weakSoundness (assumptions table h_table) (constraints table h_table)
      all_guarantees).1

end Ensemble
end Air.Flat
