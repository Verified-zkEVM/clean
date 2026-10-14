module

public import Clean.Air.BalanceModel
public import Clean.Air.OrderedChannel

/-!
# Ordered channels under an explicit balance model

The staged construction of `Clean.Air.OrderedChannel`, with the balance model as an explicit
parameter: balance is `BalanceModel.Balanced` and consistency `RawChannel.ConsistentWith`. The
legacy notions are the `BalanceModel.logUp` instances, by definition or through
`SoundEnsemble.withLogUp` and `SoundEnsembleWith.toSoundEnsemble`. The induction proofs
duplicate those of `Clean.Air.OrderedChannel`, which could become wrappers once that file's
definitions are split from its theorems.

`SoundEnsembleWith F model PublicIO` takes typed channels through `BalanceModel.Reads`
(`addChannel`, `addFinishedChannel`), so a channel of the wrong kind is a type error, and raw
channels through `[channel.ConsistentWith model]` (`addRawChannel`, `addFinishedRawChannel`).
Unlike `SoundEnsemble`, it records the consistency of every channel, not only the finished
ones, because `FormalEnsembleWith` demands it.
-/

@[expose] public section

variable {F : Type} [FiniteField F] [DecidableEq F]
open Air.Flat (Component Table Tables)

/--
`PartialBalancedChannel` under an explicit balance model: the known interactions with the
channel, together with the unknown interactions of tables added later, are balanced under the
model; the extra interactions are with the same channel; and either the known tables assume
nothing on the channel or the extra interactions meet their requirements.
-/
def PartialBalancedChannelWith (model : BalanceModel F) (tables : Tables F)
    (channel : RawChannel F) : Prop :=
  ∃ extraInteractions : List (Interaction F),
    model.Balanced (tables.interactionsWith channel ++ extraInteractions) ∧
    (∀ i ∈ extraInteractions, i.channel = channel) ∧
    (channel ∉ tables.tables.flatMap (·.channelsWithGuarantees) ∨
      ∀ i ∈ extraInteractions, i.Requirements tables.data)

/-- The legacy partial balance is partial balance under the LogUp model, by definition. -/
theorem partialBalancedChannel_iff_partialBalancedChannelWith_logUp (tables : Tables F)
    (channel : RawChannel F) :
    PartialBalancedChannel tables channel ↔ PartialBalancedChannelWith (.logUp F) tables channel :=
  Iff.rfl

variable {model : BalanceModel F}

/-- Partial balance is weaker than balance. -/
lemma partialBalancedChannelWith_of_balanced {tables : Tables F} {channel : RawChannel F} :
    model.Balanced (tables.interactionsWith channel) →
    PartialBalancedChannelWith model tables channel := by
  intro balanced
  refine ⟨[], ?_, by simp, by simp⟩
  rw [List.append_nil]
  exact balanced

/-- For ordered channels, partial balance descends to an initial sublist of the tables. -/
theorem partialBalancedChannelWith_of_cons_of_orderedChannelLt
    {table : Table F} {tables : Tables F} (same_data : table.data = tables.data)
    {channel : RawChannel F} :
    table.Constraints →
    PartialBalancedChannelWith model (.cons table tables same_data) channel →
    OrderedChannelLt channel tables.components [table.component] →
      PartialBalancedChannelWith model tables channel := by
  rintro table_constraints ⟨ extraInteractions, balanced, same_channel, extra_reqs_or_no_grts ⟩
    not_in_reqs_or
  use table.interactionsWith channel ++ extraInteractions
  simp only [circuit_norm] at *
  simp [or_imp] at ⊢ not_in_reqs_or extra_reqs_or_no_grts
  constructor
  · apply model.balanced_of_perm balanced
    grw [List.perm_append_comm_assoc]
  constructor
  · intro a
    use Table.channel_eq_of_mem_interactionsWith
    exact same_channel a
  rw [forall_and]
  rcases not_in_reqs_or with channel_not_in_grts | channel_not_in_reqs
  · simp_all
  rcases extra_reqs_or_no_grts with no_grts | extra_reqs
  · simp_all
  · right
    have channel_reqs :=
      table.requirements_of_not_mem_of_constraints table_constraints channel_not_in_reqs
    rw [Table.channelRequirements_iff_forall, same_data] at channel_reqs
    exact ⟨ channel_reqs, extra_reqs ⟩

/--
The induction step of the ordered-channel argument under a model: the channel requirements of
the old tables give the channel guarantees of one new table, through the channel's consistency
under the model.
-/
lemma guarantees_of_requirements_cons_with
    {table : Table F} {tables : Tables F} (same_data : table.data = tables.data)
    {channel : RawChannel F} [channel.ConsistentWith model] :
    table.Constraints →
    OrderedChannelRefl channel table.component →
    PartialBalancedChannelWith model (tables.cons table same_data) channel →
    (∀ table ∈ tables.tables, table.ChannelRequirements channel) →
      table.ChannelGuarantees channel := by
  rintro table_constraints ordered_channel partial_balance ih
  simp only [circuit_norm] at ordered_channel
  rcases ordered_channel with grts | reqs
  · exact table.guarantees_of_not_mem grts
  replace reqs := table.requirements_of_not_mem_of_constraints table_constraints reqs
  rcases partial_balance with ⟨ extraInteractions, balanced, same_channel, grts | extra_reqs ⟩
  · simp only [circuit_norm] at grts
    exact table.guarantees_of_not_mem grts.left
  set channelInteractions :=
    (tables.cons table same_data).interactionsWith channel ++ extraInteractions
  have subset_channelInteractions : table.interactionsWith channel ⊆ channelInteractions := by
    simp only [channelInteractions, circuit_norm]
  suffices all_grts : ∀ i ∈ channelInteractions, i.Guarantees tables.data by
    rw [Table.channelGuarantees_iff_forall, same_data]
    intro i hi
    exact all_grts i (subset_channelInteractions hi)
  have all_reqs : ∀ i ∈ channelInteractions, i.channel = channel ∧ i.Requirements tables.data := by
    simp only [channelInteractions, circuit_norm]
    intro i h_mem
    rcases h_mem with h_mem_table | h_mem_old | h_mem_extra
    · rw [Table.channelRequirements_iff_forall, same_data] at reqs
      use table.channel_eq_of_mem_interactionsWith h_mem_table
      exact reqs _ h_mem_table
    · obtain ⟨ table', h_table', i_mem_table ⟩ := h_mem_old
      simp only [Table.channelRequirements_iff_forall] at ih
      specialize ih table' h_table'
      simp only [tables.same_data _ h_table'] at ih
      use table'.channel_eq_of_mem_interactionsWith i_mem_table
      exact ih i i_mem_table
    · exact ⟨ same_channel i h_mem_extra, extra_reqs i h_mem_extra ⟩
  exact ‹channel.ConsistentWith model›.consistent channelInteractions tables.data balanced all_reqs

/--
Partial balance descends to a sublist of the tables, as long as none of the other tables adds
requirements on the channel.
-/
lemma partialBalancedChannelWith_of_sublist {subtables tables : Tables F} {channel : RawChannel F} :
    PartialBalancedChannelWith model tables channel →
    (∃ otherTables, tables.tables.Perm (subtables.tables ++ otherTables) ∧
      (∀ table ∈ otherTables, table.Constraints) ∧
      ∀ table ∈ otherTables, channel ∉ table.channelsWithRequirements) →
      PartialBalancedChannelWith model subtables channel := by
  rintro ⟨ extraInteractions, balanced, same_channel, no_grts_or_extra_reqs ⟩ subset_tables
  obtain ⟨ otherTables, perm, otherConstraints, otherReqs ⟩ := subset_tables
  by_cases subtables_empty : subtables.tables = []
  · -- nothing is known: every interaction is extra, and no known table assumes anything
    refine ⟨ tables.interactionsWith channel ++ extraInteractions, ?_, ?_, ?_ ⟩
    · simp only [Tables.interactionsWith, subtables_empty, List.flatMap_nil, List.nil_append]
      exact balanced
    · intro i hi
      rcases List.mem_append.mp hi with hi | hi
      · obtain ⟨ table, _, hi ⟩ := List.mem_flatMap.mp hi
        exact table.channel_eq_of_mem_interactionsWith hi
      · exact same_channel i hi
    · left
      simp [subtables_empty]
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
  · simp [circuit_norm, or_imp]
    constructor
    · intro i
      use fun _ _ => Table.channel_eq_of_mem_interactionsWith
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
    rw [← tables.same_data _ ht', ← Table.channelRequirements_iff_forall]
    apply Table.requirements_of_not_mem_of_constraints
    exact otherConstraints _ ht
    exact otherReqs _ ht
  apply model.balanced_of_perm balanced
  simp only [Tables.interactionsWith]
  grw [← List.append_assoc, List.perm_append_right_iff, ← List.flatMap_append, perm.flatMap]
  exact fun _ _ => List.Perm.refl _

/--
The induction step for several new tables at once, none of which adds requirements on the
channel. This is what adding a VM on top of a finished ensemble uses.
-/
lemma guarantees_of_requirements_append_with
    {ts ss : Tables F} (same_data : ts.data = ss.data)
    {channel : RawChannel F} [channel.ConsistentWith model] :
    (∀ table ∈ ts.tables, table.Constraints) →
    (∀ table ∈ ts.tables, channel ∉ table.component.circuit.channelsWithRequirements) →
    PartialBalancedChannelWith model (ts.append ss same_data) channel →
    (∀ table ∈ ss.tables, table.ChannelRequirements channel) →
      ∀ table ∈ ts.tables, table.ChannelGuarantees channel := by
  rintro constraints reqs partial_balance ih table h_table
  have same_data' : table.data = ss.data := by
    rw [ts.same_data _ h_table, same_data]
  apply guarantees_of_requirements_cons_with (model := model) (tables := ss) same_data'
    (constraints _ h_table) ?_ ?_ ih
  · right; exact reqs _ h_table
  apply partialBalancedChannelWith_of_sublist partial_balance
  obtain ⟨ i, hi, h' ⟩ := List.getElem_of_mem h_table
  symm at h'; subst h'
  use ts.tables.eraseIdx i
  constructor
  · simp [circuit_norm]
    grw [List.perm_append_comm, List.perm_cons_append_cons _ List.perm_rfl,
      List.perm_append_left_iff, List.perm_comm]
    apply List.getElem_cons_eraseIdx_perm
  constructor
  · intro t' ht'
    exact constraints _ (List.mem_of_mem_eraseIdx ht')
  · intro t' ht'
    apply reqs _ (List.mem_of_mem_eraseIdx ht')

/--
`SoundChannels` under an explicit balance model: every table's assumed channels are finished,
every finished channel is ordered on the tables, and every finished channel is consistent under
the model. Like the legacy notion, it is checkable from each table's `channelsWithGuarantees`
and `channelsWithRequirements` alone.
-/
@[circuit_norm]
def SoundChannelsWith (model : BalanceModel F) (tables : List (Component F))
    (finished : List (RawChannel F)) : Prop :=
  (∀ table ∈ tables, table.circuit.channelsWithGuarantees ⊆ finished) ∧
  (∀ channel ∈ finished, OrderedChannel channel tables) ∧
  ∀ channel ∈ finished, channel.ConsistentWith model

/-- `SoundChannelsWith` proves the spec, and the guarantees and requirements on all finished
channels, of every table, from constraints and partial balance under the model. -/
theorem spec_and_guarantees_of_soundChannelsWith {witness : Tables F}
    {finished : List (RawChannel F)} :
    SoundChannelsWith model (witness.tables.map (·.component)) finished →
    witness.Assumptions →
    witness.Constraints →
    (∀ channel ∈ finished, PartialBalancedChannelWith model witness channel) →
      ∀ table ∈ witness.tables, table.Spec ∧ ∀ channel ∈ finished,
      table.ChannelGuarantees channel ∧ table.ChannelRequirements channel := by
  rintro ⟨ subset_finished, ordered_channels, consistent_channels ⟩ assumptions constraints
    partial_balance
  induction witness using Tables.induct
  · intro _ h_table; nomatch h_table
  rename_i table tables same_data ih
  simp only [Tables.Assumptions, Tables.Constraints, circuit_norm] at *
  simp only [forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at *
  have partial_balance' c hc := by
    apply partialBalancedChannelWith_of_cons_of_orderedChannelLt same_data constraints.left
      (partial_balance c hc)
    rw [OrderedChannelLt]
    simp only [Tables.components, List.flatMap_singleton]
    rcases (ordered_channels c hc).2.2 with no_grts | no_reqs
    · left
      intro h_component
      rcases List.mem_flatMap.mp h_component with ⟨component, h_component, h_channel⟩
      rcases List.mem_map.mp h_component with ⟨table, h_table, rfl⟩
      exact no_grts table h_table h_channel
    · right
      simpa using no_reqs
  specialize ih subset_finished.right (fun c hc => (ordered_channels c hc).right.left)
    assumptions.right constraints.right partial_balance'
  constructor; swap
  · exact ih
  rw [iff_guarantees_of_constraints assumptions.left constraints.left subset_finished.left]
  intro channel h_channel
  have : channel.ConsistentWith model := consistent_channels _ h_channel
  have orderedChannelRefl : OrderedChannelRefl channel table.component := by
    simp only [circuit_norm, ordered_channels channel h_channel]
  apply guarantees_of_requirements_cons_with same_data
    constraints.left orderedChannelRefl (partial_balance channel h_channel)
  intro t ht
  exact (ih t ht).right _ h_channel |>.right

/-- The finished list can grow by any channels consistent under the model. -/
lemma soundChannelsWith_of_subset {tables : List (Component F)}
    {finished finished' : List (RawChannel F)} :
    SoundChannelsWith model tables finished →
    finished ⊆ finished' →
    (∀ channel ∈ finished', channel.ConsistentWith model) →
      SoundChannelsWith model tables finished' := by
  rintro ⟨ subset_finished, ordered_channels, _ ⟩ finished'_subset finished'_consistent
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

/-- One consistent channel can be marked finished. -/
lemma soundChannelsWith_cons {tables : List (Component F)}
    {finished : List (RawChannel F)} {channel : RawChannel F} [channel.ConsistentWith model] :
    SoundChannelsWith model tables finished →
      SoundChannelsWith model tables (channel :: finished) := by
  intro sound_channels
  apply soundChannelsWith_of_subset sound_channels
  · simp
  simp_all [SoundChannelsWith]

namespace Air.Flat
variable {PublicIO : TypeMap} [ProvableType PublicIO]

namespace Ensemble
@[circuit_norm]
abbrev SoundChannelsWith (model : BalanceModel F) (ens : Ensemble F PublicIO)
    (finished : List (RawChannel F)) : Prop :=
  _root_.SoundChannelsWith model ens.allTables finished

/-- `TableSoundness` under an explicit balance model: constraints and balance under the model
give the spec of every table. -/
@[circuit_norm]
def TableSoundnessWith (model : BalanceModel F) (ens : Ensemble F PublicIO) : Prop :=
  ∀ (witness : EnsembleWitness ens),
    witness.Assumptions →
    witness.Constraints →
    witness.BalancedChannelsWith model →
    witness.Spec

/-- The legacy table soundness is table soundness under the LogUp model, by definition. -/
theorem tableSoundness_iff_tableSoundnessWith_logUp (ens : Ensemble F PublicIO) :
    ens.TableSoundness ↔ ens.TableSoundnessWith (.logUp F) := Iff.rfl

theorem soundnessWith_of_tableSoundnessWith_and_specConsistency (ens : Ensemble F PublicIO)
    (Assumptions Spec : PublicIO F → Prop) :
    ens.TableSoundnessWith model →
    ens.AssumptionsConsistency Assumptions →
    ens.SpecConsistency Spec →
      ens.SoundnessWith model Assumptions Spec := by
  simp only [SoundnessWith, TableSoundnessWith, AssumptionsConsistency, SpecConsistency,
    StatementWith, forall_exists_index, and_imp]
  intro table_soundness assumptions_consistency spec_consistency
    publicInput assumptions witness publicInput_eq constraints balance
  simp only [← publicInput_eq] at *
  apply spec_consistency witness
  apply table_soundness witness ?assumptions constraints balance
  exact assumptions_consistency witness assumptions

/-- `SoundChannelsWith` implies `TableSoundnessWith`. -/
theorem tableSoundnessWith_of_soundChannelsWith {ens : Ensemble F PublicIO} :
    (∃ finished, finished ⊆ ens.channels ∧ ens.SoundChannelsWith model finished) →
      ens.TableSoundnessWith model := by
  intro ⟨ finished, finished_subset, soundChannels ⟩ witness assumptions constraints balance
    table h_table
  have partial_balance :
      ∀ channel ∈ finished, PartialBalancedChannelWith model witness channel := by
    intro channel h_channel
    apply partialBalancedChannelWith_of_balanced
    exact balance _ <| finished_subset h_channel
  apply spec_and_guarantees_of_soundChannelsWith ?soundChannels ?assumptions ?constraints
    partial_balance table h_table |>.left
  <;> (simp only [circuit_norm]; assumption)

theorem empty_soundChannelsWith : (empty F PublicIO).SoundChannelsWith model [] := by
  simp only [circuit_norm]

theorem empty_tableSoundnessWith : (empty F PublicIO).TableSoundnessWith model :=
  tableSoundnessWith_of_soundChannelsWith ⟨ [], List.Subset.refl [], empty_soundChannelsWith ⟩

theorem orderedChannels_of_soundChannelsWith_addTable (ens : Ensemble F PublicIO)
    (table : Component F) {finished : List (RawChannel F)} :
    ens.SoundChannelsWith model finished →
    ens.verifier = .empty F PublicIO →
    table.circuit.channelsWithGuarantees ⊆ finished →
    (∀ channel ∈ finished, channel ∉ table.circuit.channelsWithRequirements) →
    (ens.addTable table).OrderedChannels finished := by
  intro h_sound verifier_empty grts_subset_finished reqs_disjoint_finished channel h_channel
  simp only [circuit_norm, verifier_empty, allTables] at h_sound ⊢
  simp_all

theorem soundChannelsWith_markFinished (ens : Ensemble F PublicIO)
    {finished : List (RawChannel F)} (h_sound : ens.SoundChannelsWith model finished)
    (channel : RawChannel F) [channel.ConsistentWith model] :
    ens.SoundChannelsWith model (channel :: finished) :=
  soundChannelsWith_cons h_sound
end Ensemble

/--
A sound ensemble under an explicit balance model: the counterpart of `SoundEnsemble`. Every
channel it holds is consistent under the model (`channels_consistent`), which is what
`FormalEnsembleWith.consistent` demands of the bundle `toFormal` produces; the finished
channels are the ones whose guarantees the tables may assume, ordered on the tables.
-/
structure SoundEnsembleWith (F : Type) [FiniteField F] [DecidableEq F] (model : BalanceModel F)
    (PublicIO : TypeMap) [ProvableType PublicIO] extends ensemble : Ensemble F PublicIO where
  finished : List (RawChannel F)
  channels_consistent : ∀ channel ∈ channels, channel.ConsistentWith model
  finished_subset : finished ⊆ channels
  subset_finished : ensemble.channelsWithGuarantees ⊆ finished
  ordered_channels : ensemble.OrderedChannels finished
  verifier_empty : ensemble.verifier = .empty F PublicIO

attribute [circuit_norm] SoundEnsembleWith.channels_consistent SoundEnsembleWith.finished_subset
  SoundEnsembleWith.subset_finished SoundEnsembleWith.ordered_channels
  SoundEnsembleWith.verifier_empty

namespace SoundEnsembleWith
lemma finished_consistent (soundEns : SoundEnsembleWith F model PublicIO) :
    ∀ channel ∈ soundEns.finished, channel.ConsistentWith model :=
  fun channel h => soundEns.channels_consistent channel (soundEns.finished_subset h)

lemma soundChannelsWith (soundEns : SoundEnsembleWith F model PublicIO) :
    soundEns.SoundChannelsWith model soundEns.finished :=
  ⟨ (Ensemble.channelsWithGuarantees_subset_iff (ens := soundEns.ensemble)).mp
      soundEns.subset_finished,
    soundEns.ordered_channels, soundEns.finished_consistent ⟩

def empty (F : Type) [FiniteField F] [DecidableEq F] (model : BalanceModel F)
    (PublicIO : TypeMap) [ProvableType PublicIO] : SoundEnsembleWith F model PublicIO where
  ensemble := .empty F PublicIO
  finished := []
  channels_consistent := by simp [circuit_norm]
  finished_subset := List.Subset.refl _
  subset_finished := by simp [circuit_norm, Ensemble.channelsWithGuarantees]
  ordered_channels := by simp [circuit_norm]
  verifier_empty := by simp [circuit_norm]

@[circuit_norm] lemma empty_tables : (empty F model PublicIO).tables = [] := rfl
@[circuit_norm] lemma empty_channels : (empty F model PublicIO).channels = [] := rfl
@[circuit_norm] lemma empty_finished : (empty F model PublicIO).finished = [] := rfl
@[circuit_norm] lemma empty_verifier : (empty F model PublicIO).verifier = .empty F PublicIO := rfl

/-- Add a table whose assumed channels are all finished and which adds no requirement on a
finished channel; the side conditions are decided by `simp [circuit_norm]`. Like every builder
here with proof arguments, the definition is in `circuit_norm`, so that `simp` unfolds it
instead of matching projection lemmas against the supplied proofs, which fails at `simp`'s
transparency. -/
@[circuit_norm]
def addTable (soundEns : SoundEnsembleWith F model PublicIO) (table : Component F)
    (grts_subset_finished : table.circuit.channelsWithGuarantees ⊆ soundEns.finished
      := by simp [circuit_norm])
    (reqs_disjoint_finished :
      ∀ channel ∈ soundEns.finished, channel ∉ table.circuit.channelsWithRequirements
      := by simp [circuit_norm]) :
    SoundEnsembleWith F model PublicIO where
  ensemble := soundEns.ensemble.addTable table
  finished := soundEns.finished
  channels_consistent := soundEns.channels_consistent
  finished_subset := soundEns.finished_subset
  subset_finished := by
    have h := soundEns.subset_finished
    simp_all [circuit_norm, Ensemble.channelsWithGuarantees_eq_verifier_append]
  ordered_channels := soundEns.orderedChannels_of_soundChannelsWith_addTable table
    soundEns.soundChannelsWith soundEns.verifier_empty grts_subset_finished reqs_disjoint_finished
  verifier_empty := soundEns.verifier_empty

variable {soundEns : SoundEnsembleWith F model PublicIO} {table : Component F}
    {gsf : table.circuit.channelsWithGuarantees ⊆ soundEns.finished}
    {rdf : ∀ channel ∈ soundEns.finished, channel ∉ table.circuit.channelsWithRequirements}

@[circuit_norm] lemma addTable_tables :
  (soundEns.addTable table gsf rdf).tables = table :: soundEns.tables := rfl
@[circuit_norm] lemma addTable_channels :
  (soundEns.addTable table gsf rdf).channels = soundEns.channels := rfl
@[circuit_norm] lemma addTable_finished :
  (soundEns.addTable table gsf rdf).finished = soundEns.finished := rfl
@[circuit_norm] lemma addTable_verifier :
  (soundEns.addTable table gsf rdf).verifier = soundEns.verifier := rfl

section Typed
variable {Message : TypeMap} [ProvableType Message]
variable {Ch : (Message : TypeMap) → [ProvableType Message] → Type} [model.Reads Ch]

/--
Add a typed channel of the kind the model reads, erased through `BalanceModel.Reads.toRaw`.
A channel of any other kind is a type error here: there is no `Reads` instance for it.
-/
def addChannel (soundEns : SoundEnsembleWith F model PublicIO) (channel : Ch Message) :
    SoundEnsembleWith F model PublicIO where
  ensemble := { soundEns.ensemble with
    channels := BalanceModel.Reads.toRaw (model := model) channel :: soundEns.channels }
  finished := soundEns.finished
  channels_consistent := by
    intro channel' h_mem
    rw [List.mem_cons] at h_mem
    rcases h_mem with rfl | h_mem
    · exact BalanceModel.Reads.consistentWith channel
    · exact soundEns.channels_consistent channel' h_mem
  finished_subset := List.subset_cons_of_subset _ soundEns.finished_subset
  subset_finished := soundEns.subset_finished
  ordered_channels := soundEns.ordered_channels
  verifier_empty := soundEns.verifier_empty

variable {channel : Ch Message}

@[circuit_norm] lemma addChannel_channels :
  (soundEns.addChannel channel).channels =
    BalanceModel.Reads.toRaw (model := model) channel :: soundEns.channels := rfl
@[circuit_norm] lemma addChannel_tables :
  (soundEns.addChannel channel).tables = soundEns.tables := rfl
@[circuit_norm] lemma addChannel_finished :
  (soundEns.addChannel channel).finished = soundEns.finished := rfl
@[circuit_norm] lemma addChannel_verifier :
  (soundEns.addChannel channel).verifier = soundEns.verifier := rfl
end Typed

/--
Add a raw channel that is consistent under the model. `ConsistentWith` instances exist only for
legacy channels under `logUp` and directed channels under `multiset`.
-/
def addRawChannel (soundEns : SoundEnsembleWith F model PublicIO) (channel : RawChannel F)
    [channel.ConsistentWith model] : SoundEnsembleWith F model PublicIO where
  ensemble := { soundEns.ensemble with channels := channel :: soundEns.channels }
  finished := soundEns.finished
  channels_consistent := by
    intro channel' h_mem
    rw [List.mem_cons] at h_mem
    rcases h_mem with rfl | h_mem
    · assumption
    · exact soundEns.channels_consistent channel' h_mem
  finished_subset := List.subset_cons_of_subset _ soundEns.finished_subset
  subset_finished := soundEns.subset_finished
  ordered_channels := soundEns.ordered_channels
  verifier_empty := soundEns.verifier_empty

section Raw
variable {channel : RawChannel F} [channel.ConsistentWith model]

@[circuit_norm] lemma addRawChannel_channels :
  (soundEns.addRawChannel channel).channels = channel :: soundEns.channels := rfl
@[circuit_norm] lemma addRawChannel_tables :
  (soundEns.addRawChannel channel).tables = soundEns.tables := rfl
@[circuit_norm] lemma addRawChannel_finished :
  (soundEns.addRawChannel channel).finished = soundEns.finished := rfl
@[circuit_norm] lemma addRawChannel_verifier :
  (soundEns.addRawChannel channel).verifier = soundEns.verifier := rfl
end Raw

/-- Mark a channel of the ensemble finished. Its consistency is already recorded, so only the
membership is owed; it is decided by `simp [circuit_norm]` after the typed builders, since
`circuit_norm` rewrites `Reads.toRaw` to the channel's own `toRaw`. -/
@[circuit_norm]
def markFinished (soundEns : SoundEnsembleWith F model PublicIO) (channel : RawChannel F)
    (h_mem : channel ∈ soundEns.channels := by simp [circuit_norm]) :
    SoundEnsembleWith F model PublicIO where
  ensemble := soundEns.ensemble
  finished := channel :: soundEns.finished
  channels_consistent := soundEns.channels_consistent
  finished_subset := List.cons_subset.mpr ⟨ h_mem, soundEns.finished_subset ⟩
  subset_finished := List.subset_cons_of_subset _ soundEns.subset_finished
  ordered_channels := by
    have : channel.ConsistentWith model := soundEns.channels_consistent channel h_mem
    exact (soundEns.soundChannelsWith_markFinished soundEns.soundChannelsWith channel).right.left
  verifier_empty := soundEns.verifier_empty

section Finished
variable {channel : RawChannel F} {h_mem : channel ∈ soundEns.channels}

@[circuit_norm] lemma markFinished_channels :
  (soundEns.markFinished channel h_mem).channels = soundEns.channels := rfl
@[circuit_norm] lemma markFinished_tables :
  (soundEns.markFinished channel h_mem).tables = soundEns.tables := rfl
@[circuit_norm] lemma markFinished_finished :
  (soundEns.markFinished channel h_mem).finished = channel :: soundEns.finished := rfl
@[circuit_norm] lemma markFinished_verifier :
  (soundEns.markFinished channel h_mem).verifier = soundEns.verifier := rfl
end Finished

section Typed
variable {Message : TypeMap} [ProvableType Message]
variable {Ch : (Message : TypeMap) → [ProvableType Message] → Type} [model.Reads Ch]

/-- Add a typed channel of the kind the model reads and mark it finished at once. -/
def addFinishedChannel (soundEns : SoundEnsembleWith F model PublicIO) (channel : Ch Message) :
    SoundEnsembleWith F model PublicIO :=
  soundEns
    |>.addChannel channel
    |>.markFinished (BalanceModel.Reads.toRaw (model := model) channel) (List.mem_cons_self ..)

variable {channel : Ch Message}

@[circuit_norm] lemma addFinishedChannel_channels :
  (soundEns.addFinishedChannel channel).channels =
    BalanceModel.Reads.toRaw (model := model) channel :: soundEns.channels := rfl
@[circuit_norm] lemma addFinishedChannel_tables :
  (soundEns.addFinishedChannel channel).tables = soundEns.tables := rfl
@[circuit_norm] lemma addFinishedChannel_finished :
  (soundEns.addFinishedChannel channel).finished =
    BalanceModel.Reads.toRaw (model := model) channel :: soundEns.finished := rfl
@[circuit_norm] lemma addFinishedChannel_verifier :
  (soundEns.addFinishedChannel channel).verifier = soundEns.verifier := rfl
end Typed

/-- Add a consistent raw channel and mark it finished at once. -/
def addFinishedRawChannel (soundEns : SoundEnsembleWith F model PublicIO) (channel : RawChannel F)
    [channel.ConsistentWith model] : SoundEnsembleWith F model PublicIO :=
  soundEns
    |>.addRawChannel channel
    |>.markFinished channel (List.mem_cons_self ..)

section Raw
variable {channel : RawChannel F} [channel.ConsistentWith model]

@[circuit_norm] lemma addFinishedRawChannel_channels :
  (soundEns.addFinishedRawChannel channel).channels = channel :: soundEns.channels := rfl
@[circuit_norm] lemma addFinishedRawChannel_tables :
  (soundEns.addFinishedRawChannel channel).tables = soundEns.tables := rfl
@[circuit_norm] lemma addFinishedRawChannel_finished :
  (soundEns.addFinishedRawChannel channel).finished = channel :: soundEns.finished := rfl
@[circuit_norm] lemma addFinishedRawChannel_verifier :
  (soundEns.addFinishedRawChannel channel).verifier = soundEns.verifier := rfl
end Raw

/-- The formal ensemble under the model: its `consistent` field is the record's, and its
soundness is the ordered-channel argument under the model. -/
@[circuit_norm]
def toFormal (soundEns : SoundEnsembleWith F model PublicIO)
    (Assumptions Spec : PublicIO F → Prop)
    (assumptionsConsistency : soundEns.AssumptionsConsistency Assumptions)
    (specConsistency : soundEns.SpecConsistency Spec) :
    FormalEnsembleWith F model PublicIO where
  ensemble := soundEns.ensemble
  Assumptions := Assumptions
  Spec := Spec
  consistent := soundEns.channels_consistent
  soundness := by
    apply soundEns.soundnessWith_of_tableSoundnessWith_and_specConsistency
      Assumptions Spec ?_ assumptionsConsistency specConsistency
    apply soundEns.tableSoundnessWith_of_soundChannelsWith
    use soundEns.finished, soundEns.finished_subset
    exact soundEns.soundChannelsWith

section Formal
variable {Assumptions Spec : PublicIO F → Prop}
  {ac : soundEns.AssumptionsConsistency Assumptions} {sc : soundEns.SpecConsistency Spec}

@[circuit_norm] lemma toFormal_ensemble :
  (soundEns.toFormal Assumptions Spec ac sc).ensemble = soundEns.ensemble := rfl
@[circuit_norm] lemma toFormal_assumptions :
  (soundEns.toFormal Assumptions Spec ac sc).Assumptions = Assumptions := rfl
@[circuit_norm] lemma toFormal_spec :
  (soundEns.toFormal Assumptions Spec ac sc).Spec = Spec := rfl
end Formal

/-- A sound ensemble under the LogUp model is a legacy sound ensemble: pointwise through
`consistent_iff_consistentWith_logUp`, not by definition, since the two records differ in
which consistency they carry. -/
def toSoundEnsemble (soundEns : SoundEnsembleWith F (.logUp F) PublicIO) :
    SoundEnsemble F PublicIO where
  ensemble := soundEns.ensemble
  finished := soundEns.finished
  finished_consistent channel h :=
    (RawChannel.consistent_iff_consistentWith_logUp channel).mpr
      (soundEns.finished_consistent channel h)
  finished_subset := soundEns.finished_subset
  subset_finished := soundEns.subset_finished
  ordered_channels := soundEns.ordered_channels
  verifier_empty := soundEns.verifier_empty
end SoundEnsembleWith

/-- A legacy sound ensemble whose channels are all consistent is a sound ensemble under the
LogUp model. Every directed channel is consistent under LogUp, so a directed channel can enter
here; the resulting statement is met only by inactive traces. -/
def SoundEnsemble.withLogUp (soundEns : SoundEnsemble F PublicIO)
    (consistent : ∀ channel ∈ soundEns.channels, channel.Consistent) :
    SoundEnsembleWith F (.logUp F) PublicIO where
  ensemble := soundEns.ensemble
  finished := soundEns.finished
  channels_consistent channel h :=
    (RawChannel.consistent_iff_consistentWith_logUp channel).mp (consistent channel h)
  finished_subset := soundEns.finished_subset
  subset_finished := soundEns.subset_finished
  ordered_channels := soundEns.ordered_channels
  verifier_empty := soundEns.verifier_empty
end Air.Flat
