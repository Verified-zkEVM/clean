module

public import Clean.Air.FlatEnsemble

@[expose] public section

/-!
# Soundness by channel finishing order

`OrderedChannel` orders tables: on each channel, every table that pushes comes before every table
that pulls, and no table does both. That rules out a table whose requirements on one channel follow
from its guarantees on *another*. A counted pull is the case that needs this: its multiplicity owes
`CountUpTo N`, and for a bound too large to constrain arithmetically that comes from range-checking
the multiplicity on a second channel. `Clean/Examples/CountedSquares` counts to `2` and constrains
its count in the circuit, which is why one finished channel is enough there.

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
      stagedRequirements_of_forall fun c e ⟨later, hl⟩ =>
        h c e ⟨channel :: later, by simp [hl]⟩⟩

/-!
## Stages: a channel and a class of its messages

A channel that one table both pulls from and pushes to, on different messages, is not a cycle: what
it reads and what it writes are disjoint. A bus shared by several operations is where this happens.
A table that answers one operation by using the answers to others pulls those answers and pushes
its own, all under one channel name, and ordering whole channels cannot express that. Ordering by
stage, a channel together with a class of its messages, lets the class it pushes be finished after
the classes it pulls. Balance is message by message (`BalancedUpTo.filter_msg`), so each stage
balances by itself, and a whole channel is the stage whose class is every message. Genuine cycles
still have no valid order.
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
  rw [guarantees_iff_channelGuarantees]
  intro c h_c
  rw [channelGuarantees_iff_forall]
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
  requirementsAfterOn_of_covered fun _ _ c h_c i _ _ => h c h_c i.msg

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

/-- The stage that is a whole channel. -/
def Stage.ofChannel (channel : RawChannel F) : Stage F := { channel }

@[simp] lemma Stage.channel_ofChannel (channel : RawChannel F) :
    (ofChannel channel).channel = channel := rfl

lemma Component.stagedRequirementsOn_of_stagedRequirements
    {component : Component F} :
    ∀ {finished : List (RawChannel F)}, component.StagedRequirements finished →
      component.StagedRequirementsOn (finished.map Stage.ofChannel)
  | [], _ => trivial
  | _ :: _, ⟨after, rest⟩ =>
    ⟨ requirementsAfterOn_of_requirementsAfter after
        fun c hc => ⟨Stage.ofChannel c, List.mem_map_of_mem hc, rfl, fun _ => rfl⟩,
      stagedRequirementsOn_of_stagedRequirements rest ⟩

namespace Ensemble
variable {PublicIO : TypeMap} [ProvableType PublicIO]

/-- Every table's guarantees on every stage hold, by induction from the oldest stage. -/
theorem guaranteesOn_of_stagedRequirementsOn {ens : Ensemble F PublicIO} {N : ℕ}
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
    have ih := guaranteesOn_of_stagedRequirementsOn verifier_empty witness assumptions
      constraints balanced
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
theorem tableSoundness_of_stagedRequirementsOn {ens : Ensemble F PublicIO} {balance : Balance F}
    (finished : List (Stage F))
    (verifier_empty : ens.verifier = .empty F PublicIO)
    (finished_channels : ∀ s ∈ finished, s.channel ∈ ens.channels)
    (covered : ∀ component ∈ ens.tables, ∀ c ∈ component.circuit.channelsWithGuarantees,
      ∀ msg, ∃ s ∈ finished, s.channel = c ∧ s.cls msg)
    (consistent : ∀ s ∈ finished, s.channel.ConsistentUpTo balance.pullBound)
    (staged : ∀ component ∈ ens.tables, component.StagedRequirementsOn finished) :
    ens.TableSoundness balance := by
  intro witness assumptions constraints fit balanced
  have guarantees := guaranteesOn_of_stagedRequirementsOn verifier_empty witness assumptions
    constraints
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

/-!
### The channel form

A whole channel is the stage whose class is every message, so a finishing order of channels is the
finishing order of those stages, and the theorem below is the stage one read through that
correspondence. The statement is kept because an ensemble whose channels finish whole is the
simpler thing to say, and to use.
-/

/--
Soundness from channel finishing order: if every table's guarantees come from finished channels,
every finished channel is consistent under the balance check, and every component's requirements
on a finished channel follow from its guarantees on the channels finished before it, then the
tables are sound.
-/
theorem tableSoundness_of_stagedRequirements {ens : Ensemble F PublicIO} {balance : Balance F}
    (finished : List (RawChannel F))
    (verifier_empty : ens.verifier = .empty F PublicIO)
    (finished_subset : finished ⊆ ens.channels)
    (subset_finished : ∀ component ∈ ens.tables,
      component.circuit.channelsWithGuarantees ⊆ finished)
    (consistent : ∀ channel ∈ finished, channel.ConsistentUpTo balance.pullBound)
    (staged : ∀ component ∈ ens.tables, component.StagedRequirements finished) :
    ens.TableSoundness balance :=
  tableSoundness_of_stagedRequirementsOn (finished.map Stage.ofChannel) verifier_empty
    (by simpa using fun _ h => finished_subset h)
    (fun component h c h_c _ => ⟨Stage.ofChannel c,
      List.mem_map_of_mem (subset_finished component h h_c), rfl, rfl⟩)
    (by simpa using consistent)
    (fun component h => Component.stagedRequirementsOn_of_stagedRequirements (staged component h))

end Ensemble
end Air.Flat
