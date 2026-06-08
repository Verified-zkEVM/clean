import Clean.Air.FlatEnsemble

variable {F : Type} [Field F]
open Air.Flat (Component Table Tables)

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
def OrderedChannel (channel : RawChannel F) (tables : List (Component F)) : Prop :=
  ∀ i (hi : i < tables.length) j (hj : j < tables.length),
    channel ∈ tables[i].circuit.channelsWithGuarantees →
    channel ∈ tables[j].circuit.channelsWithRequirements →
      i < j

@[circuit_norm]
lemma orderedChannel_nil (channel : RawChannel F) : OrderedChannel channel [] := by
  simp [OrderedChannel]

@[circuit_norm]
abbrev OrderedChannelRefl (channel : RawChannel F) (table : Component F) : Prop :=
  channel ∉ table.circuit.channelsWithGuarantees ∨ channel ∉ table.circuit.channelsWithRequirements

abbrev OrderedChannelLt (channel : RawChannel F) (tables₁ tables₂ : List (Component F)) : Prop :=
  channel ∉ tables₁.flatMap (·.circuit.channelsWithGuarantees) ∨ channel ∉ tables₂.flatMap (·.circuit.channelsWithRequirements)

@[circuit_norm]
lemma orderedChannelLt_nil_right (channel : RawChannel F) (tables : List (Component F)) :
    OrderedChannelLt channel tables [] := by simp [OrderedChannelLt]

@[circuit_norm]
lemma orderedChannelLt_nil_left (channel : RawChannel F) (tables : List (Component F)) :
    OrderedChannelLt channel [] tables := by simp [OrderedChannelLt]

@[circuit_norm]
lemma orderedChannelLt_cons_right (channel : RawChannel F) {table : Component F} {ts ss : List (Component F)} :
  OrderedChannelLt channel ss (table :: ts) ↔
    (channel ∉ ss.flatMap (·.circuit.channelsWithGuarantees) ∨ channel ∉ table.circuit.channelsWithRequirements) ∧
    OrderedChannelLt channel ss ts := by
  simp [OrderedChannelLt, circuit_norm]
  tauto

@[circuit_norm]
lemma orderedChannelLt_append_left {channel : RawChannel F} {ts₁ ts₂ ss : List (Component F)} :
  OrderedChannelLt channel (ts₁ ++ ts₂) ss ↔
    OrderedChannelLt channel ts₁ ss ∧ OrderedChannelLt channel ts₂ ss := by
  simp only [OrderedChannelLt, circuit_norm]
  tauto

@[circuit_norm]
lemma orderedChannelLt_append_right {channel : RawChannel F} {ts ss₁ ss₂ : List (Component F)} :
  OrderedChannelLt channel ts (ss₁ ++ ss₂) ↔
    OrderedChannelLt channel ts ss₁ ∧ OrderedChannelLt channel ts ss₂ := by
  simp only [OrderedChannelLt, circuit_norm]
  tauto

@[circuit_norm]
lemma orderedChannel_cons (table : Component F) (tables : List (Component F)) (channel : RawChannel F) :
  OrderedChannel channel (table :: tables) ↔
  OrderedChannelRefl channel table ∧ OrderedChannel channel tables ∧ OrderedChannelLt channel tables [table] := by
  simp only [circuit_norm, OrderedChannel, OrderedChannelRefl, List.length_cons]
  -- Intuition: The `i < j` conclusion of `OrderedChannel` falsifies the hypotheses if `j = 0`,
  -- so apart from the "induction hypothesis" where `i, j > 0`, we get two distinct statements by specializing to `i = 0` and `i > 0` respectively
  simp only [Nat.forall_lt_succ_left', List.getElem_cons_zero, List.getElem_cons_succ]
  simp only [lt_self_iff_false, imp_false, lt_add_iff_pos_left, Order.lt_add_one_iff, zero_le,
    implies_true, and_true, not_lt_zero, Order.add_one_le_iff]
  rw [forall₂_and, List.forall_mem_iff_getElem, or_iff_not_imp_left, or_iff_not_imp_left]
  push_neg
  simp only [exists_imp]
  tauto

lemma orderedChannel_singleton_iff (table : Component F) (channel : RawChannel F) :
    OrderedChannel channel [table] ↔ OrderedChannelRefl channel table := by
  simp [circuit_norm]

/-- Alternative, and sometimes more convenient, formulation of `OrderedChannel` -/
lemma orderedChannel_iff (tables : List (Component F)) (channel : RawChannel F) :
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
lemma orderedChannel_append (ts ss : List (Component F)) (channel : RawChannel F) :
  OrderedChannel channel (ts ++ ss) ↔
    OrderedChannel channel ts ∧ OrderedChannel channel ss ∧ OrderedChannelLt channel ss ts := by
  simp only [orderedChannel_iff]
  constructor
  · rintro ⟨ordered_refl, ordered_split⟩
    simp_all
    constructor
    · intro ts' ss' h_append
      have hlt := ordered_split ts' (ss' ++ ss) (by simp [h_append])
      rw [orderedChannelLt_append_left] at hlt
      tauto
    · intro ts' ss' h_append
      have hlt := ordered_split (ts ++ ts') ss' (by simp [h_append])
      rw [orderedChannelLt_append_right] at hlt
      tauto
  · simp only [List.append_eq_append_iff, ←exists_or]
    grind

/-- A sufficient condition for ordered channel is that there are no requirements added -/
lemma orderedChannel_of_no_requirements {channel : RawChannel F} {tables : List (Component F)} :
  (∀ table ∈ tables, channel ∉ table.circuit.channelsWithRequirements) →
    OrderedChannel channel tables := by
  intro reqs
  rw [orderedChannel_iff]
  simp_all [OrderedChannelRefl, OrderedChannelLt]

/-- A sufficient condition for ordered channel is that there are no guarantees added -/
lemma orderedChannel_of_no_guarantees {channel : RawChannel F} {tables : List (Component F)} :
  (∀ table ∈ tables, channel ∉ table.circuit.channelsWithGuarantees) →
    OrderedChannel channel tables := by
  intro grts
  rw [orderedChannel_iff]
  simp_all [OrderedChannelRefl, OrderedChannelLt]

/-- A sufficient condition for ordered channel lt is that there are no requirements added in the second list -/
lemma orderedChannelLt_of_no_requirements {channel : RawChannel F} {ts ss : List (Component F)} :
  (∀ table ∈ ts, channel ∉ table.circuit.channelsWithRequirements) →
    OrderedChannelLt channel ss ts := by
  intro no_reqs
  simp_all [OrderedChannelLt]

/-- A sufficient condition for ordered channel lt is that there are no guarantees added in the first list -/
lemma orderedChannelLt_of_no_guarantees {channel : RawChannel F} {ts ss : List (Component F)} :
  (∀ table ∈ ss, channel ∉ table.circuit.channelsWithGuarantees) →
    OrderedChannelLt channel ss ts := by
  intro no_grts
  simp_all [OrderedChannelLt]

/--
Relaxed version of BalancedChannel that works with ensembles that aren't fully specified yet,
where we assume our interactions are a subset of some larger list which is balanced.

designed to be used for proving soundness by adding one table after another.
-/
def PartialBalancedChannel [DecidableEq F] (tables : Tables F) (channel : RawChannel F) : Prop :=
  -- `extraInteractions` represents the unknown interactions from tables added later
    ∃ extraInteractions : List (Interaction F),
      -- the total of known + unknown interactions is balanced
      BalancedInteractions (tables.interactionsWith channel ++ extraInteractions) ∧
      -- guarantee-side interactions are either active pulls or disabled padding
      InteractionsWellFormed (tables.interactionsWith channel ++ extraInteractions) ∧
      -- the extra interactions are with the same channel.
      (∀ i ∈ extraInteractions, i.channel = channel) ∧
    -- additionally, we _assume_ that either the requirements on future interactions hold unconditionally,
    -- or that known interactions do not assume guarantees on the same channel.
    -- this restricts the order in which tables can be added. essentially, it requires that the `extraTables`
    -- that create the `extraInteractions` satisfy `OrderedChannelLt channel tables extraTables` (see below);
    -- and it's the missing piece when reasoning about requirements and guarantees on the full list of balanced interactions.
    (channel ∉ tables.tables.flatMap (·.channelsWithGuarantees) ∨ ∀ i ∈ extraInteractions, i.Requirements tables.data)

/-- Partial balance is trivially weaker than balance -/
lemma partialBalancedChannel_of_balancedInteractions [DecidableEq F] {tables : Tables F} {channel : RawChannel F} :
    BalancedInteractions (tables.interactionsWith channel) →
    InteractionsWellFormed (tables.interactionsWith channel) →
    PartialBalancedChannel tables channel := by
  intro balanced wellformed
  use []
  simp [balanced, wellformed]

/--
For ordered channels, we can always instantiate partial balance at an initial sublist.
-/
theorem partialBalancedChannel_of_cons_of_orderedChannelLt [DecidableEq F]
  {table : Table F} {tables : Tables F} (same_data : table.data = tables.data)
  {channel : RawChannel F} :
  PartialBalancedChannel (.cons table tables same_data) channel →
  OrderedChannelLt channel tables.components [table.component] →
    PartialBalancedChannel tables channel := by
  rintro ⟨ extraInteractions, balanced, wellformed, same_channel, extra_reqs_or_no_grts ⟩ not_in_reqs_or
  use table.interactionsWith channel ++ extraInteractions
  simp only [circuit_norm] at *
  simp [or_imp] at ⊢ not_in_reqs_or extra_reqs_or_no_grts
  constructor
  · apply balancedInteractions_of_perm balanced
    grw [List.perm_append_comm_assoc]
  constructor
  · apply wellformed.of_perm
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
    have channel_reqs := table.requirements_of_not_mem channel_not_in_reqs
    rw [Table.channelRequirements_iff_forall, same_data] at channel_reqs
    exact ⟨ channel_reqs, extra_reqs ⟩

/--
For ordered channels, we can always instantiate partial balance at an initial sublist.
-/
lemma partialBalancedChannel_of_cons_of_orderedChannel [DecidableEq F]
  {table : Table F} {tables : Tables F} (same_data : table.data = tables.data)
  {channel : RawChannel F} :
  PartialBalancedChannel (tables.cons table same_data) channel →
  OrderedChannel channel (table.component :: tables.components) →
    PartialBalancedChannel tables channel := by
  intro partial_balance ordered_channel
  apply partialBalancedChannel_of_cons_of_orderedChannelLt same_data partial_balance
  simp_all [circuit_norm]

/--
The significance of `OrderedChannel` is that it lets us prove soundness
on a list of tables by induction. This lemma captures the main step.
-/
lemma guarantees_of_requirements_cons [DecidableEq F]
  -- given a list of tables, and one additional table
  {table : Table F} {tables : Tables F} (same_data : table.data = tables.data)
  -- and a channel that is consistent, ordered on the new table, and partially balanced on the combined tables
  {channel : RawChannel F} [channel.Consistent] :
  OrderedChannelRefl channel table.component →
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
  rcases partial_balance with ⟨ extraInteractions, balanced, wellformed, same_channel, grts | extra_reqs ⟩
  · simp only [circuit_norm] at grts
    exact table.guarantees_of_not_mem grts.left
  -- now, to prove this table's channel guarantees, we show guarantees on _all_ channel interactions (that we know are balanced)
  set channelInteractions := (tables.cons table same_data).interactionsWith channel ++ extraInteractions
  have subset_channelInteractions : table.interactionsWith channel ⊆ channelInteractions := by
    simp only [channelInteractions, circuit_norm]
  suffices all_grts : ∀ i ∈ channelInteractions, i.Guarantees tables.data by
    rw [Table.channelGuarantees_iff_forall, same_data]
    intro i hi
    exact all_grts i (subset_channelInteractions hi)
  -- this works since we can prove all channel _requirements_
  -- relies on `ordered_channels` and `partial_balance` (the extra interactions assumption)
  have all_reqs : ∀ i ∈ channelInteractions, i.channel = channel ∧ i.Requirements tables.data := by
    simp only [channelInteractions, circuit_norm]
    intro i h_mem
    rcases h_mem with h_mem_table | h_mem_old | h_mem_extra
    -- for the new table, we can just use the requirements assumption
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
  -- consistent channels goes from requirements to guarantees
  -- uses `consistent_channels` and `partial_balance`
  apply ‹channel.Consistent›.consistent channelInteractions tables.data balanced wellformed all_reqs

/--
Partial balance can be specialized to a sublist (= part of a permutation),
as long as none of the extra tables add requirements.
-/
lemma partialBalancedChannel_of_sublist [DecidableEq F] {subtables tables : Tables F} {channel : RawChannel F} :
  PartialBalancedChannel tables channel →
  (∃ otherTables, tables.tables.Perm (subtables.tables ++ otherTables) ∧
    ∀ table ∈ otherTables, channel ∉ table.channelsWithRequirements) →
    PartialBalancedChannel subtables channel := by
  rintro ⟨ extraInteractions, balanced, wellformed, same_channel, no_grts_or_extra_reqs ⟩ subset_tables
  obtain ⟨ otherTables, perm, otherReqs ⟩ := subset_tables
  by_cases subtables_empty : subtables.tables = []
  · simp [subtables_empty, circuit_norm, PartialBalancedChannel, Tables.interactionsWith]
    use []
    simp [BalancedInteractions, balanceOf, InteractionsWellFormed]
    by_cases h : ringChar F = 0
    · exact Or.inr h
    · exact Or.inl (Nat.pos_of_ne_zero h)
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
    · apply wellformed.of_perm
      simp only [Tables.interactionsWith]
      grw [← List.append_assoc, List.perm_append_right_iff, ← List.flatMap_append, perm.flatMap]
      exact fun _ _ => List.Perm.refl _
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
    apply Table.requirements_of_not_mem
    exact otherReqs _ ht
  -- balance
  apply balancedInteractions_of_perm balanced
  simp only [Tables.interactionsWith]
  grw [← List.append_assoc, List.perm_append_right_iff, ← List.flatMap_append, perm.flatMap]
  exact fun _ _ => List.Perm.refl _

/--
The argument of `guarantees_of_requirements_cons`
also works for adding multiple new tables, if we make the assumption a bit stronger:
We can no longer continue to introduce guarantees for the channel.

This is relevant later when we add VM channels on top of an already finished, sound ensemble.
-/
lemma guarantees_of_requirements_append [DecidableEq F]
  -- given two lists of tables
  {ts ss : Tables F} (same_data : ts.data = ss.data)
  -- and a channel that is consistent, _doesn't add requirements_ on the new tables,
  -- and is partially balanced on the combined tables
  {channel : RawChannel F} [channel.Consistent] :
  (∀ table ∈ ts.tables, channel ∉ table.component.circuit.channelsWithRequirements) →
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
lemma iff_guarantees_of_constraints {table : Table F} {finished : List (RawChannel F)} :
  table.Assumptions →
  table.Constraints →
  table.component.circuit.channelsWithGuarantees ⊆ finished →
  ((table.Spec ∧ ∀ channel ∈ finished, table.ChannelGuarantees channel ∧ table.ChannelRequirements channel) ↔
    ∀ channel ∈ finished, table.ChannelGuarantees channel) := by
  intro assumptions constraints subset_finished
  constructor; simp_all
  intro grts
  have all_grts : table.Guarantees := by
    rw [Table.guarantees_iff_channelGuarantees]
    intro channel h_channel
    exact grts _ (subset_finished h_channel)
  -- constraints ∧ guarantees → requirements → channelRequirements
  have ⟨ spec, all_reqs ⟩ := table.weakSoundness assumptions constraints all_grts
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
def SoundChannels [DecidableEq F] (tables : List (Component F)) (finished : List (RawChannel F)) : Prop :=
  (∀ table ∈ tables, table.circuit.channelsWithGuarantees ⊆ finished) ∧
  (∀ channel ∈ finished, OrderedChannel channel tables) ∧
  ∀ channel ∈ finished, channel.Consistent

/-- `SoundChannels` lets us prove a soundness theorem. -/
theorem spec_and_guarantees_of_soundChannels [DecidableEq F] {witness : Tables F} {finished : List (RawChannel F)} :
  SoundChannels (witness.tables.map (·.component)) finished →
  -- constraints + partial balance
  witness.Assumptions →
  witness.Constraints →
  (∀ channel ∈ finished, PartialBalancedChannel witness channel) →
    -- implies the spec, and the guarantees and requirements on all finished channels
    ∀ table ∈ witness.tables, table.Spec ∧ ∀ channel ∈ finished,
    table.ChannelGuarantees channel ∧ table.ChannelRequirements channel := by
  -- by induction on the tables
  rintro ⟨ subset_finished, ordered_channels, consistent_channels ⟩ assumptions constraints partial_balance
  induction witness using Tables.induct
  · intro _ h_table; nomatch h_table
  -- induction step
  rename_i table tables same_data ih
  -- first, we use the IH
  have partial_balance' c hc := partialBalancedChannel_of_cons_of_orderedChannel
    same_data (partial_balance c hc) (ordered_channels c hc)
  simp only [Tables.Assumptions, Tables.Constraints, circuit_norm] at *
  simp only [forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at *
  specialize ih subset_finished.right (fun c hc => (ordered_channels c hc).right.left)
    assumptions.right constraints.right partial_balance'
  constructor; swap
  · exact ih
  -- it's enough to prove guarantees of all channels, since they + constraints imply requirements
  rw [iff_guarantees_of_constraints assumptions.left constraints.left subset_finished.left]
  -- the rest is just applying `guarantees_of_requirements_cons`
  intro channel h_channel
  have : channel.Consistent := consistent_channels _ h_channel
  have orderedChannelRefl : OrderedChannelRefl channel table.component := by
    simp only [circuit_norm, ordered_channels channel h_channel]
  apply guarantees_of_requirements_cons same_data
    orderedChannelRefl (partial_balance channel h_channel)
  intro t ht
  exact (ih t ht).right _ h_channel |>.right

/-- `SoundChannels` is strictly increasing: you can make the finished list bigger by any consistent channels -/
lemma soundChannels_of_soundChannels_subset [DecidableEq F] {tables : List (Component F)} {finished finished' : List (RawChannel F)} :
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
lemma soundChannels_cons_of_soundChannels [DecidableEq F] {tables : List (Component F)}
  {finished : List (RawChannel F)} {channel : RawChannel F} [channel.Consistent] :
  SoundChannels tables finished →
    SoundChannels tables (channel :: finished) := by
  intro sound_channels
  apply soundChannels_of_soundChannels_subset sound_channels
  · simp
  simp_all [SoundChannels]

namespace Air.Flat
variable {PublicIO : TypeMap} [ProvableType PublicIO]
variable [DecidableEq F]

namespace Ensemble
/-- Partial balanced channel is trivially weaker than balanced channel -/
lemma partialBalancedChannel_of_balancedChannel {ens : Ensemble F PublicIO}
    {witness : EnsembleWitness ens} (channel : RawChannel F) :
  witness.BalancedChannel channel →
    PartialBalancedChannel witness channel := by
  intro balanced
  use []
  simp_all [EnsembleWitness.BalancedChannel]

@[circuit_norm]
abbrev SoundChannels (ens : Ensemble F PublicIO) (finished : List (RawChannel F)) : Prop :=
  _root_.SoundChannels ens.allTables finished

@[circuit_norm]
abbrev OrderedChannels (ens : Ensemble F PublicIO) (finished : List (RawChannel F)) : Prop :=
  ∀ channel ∈ finished, OrderedChannel channel ens.allTables

/--
Main result of this section:
`SoundChannels` (an easily checkable property) implies
`TableSoundness`, a complex ensemble-level soundness statement.
-/
theorem tableSoundness_of_soundChannels {ens : Ensemble F PublicIO} :
  (∃ finished, finished ⊆ ens.channels ∧ ens.SoundChannels finished) →
    ens.TableSoundness := by
  intro ⟨ finished, finished_subset, soundChannels ⟩ witness assumptions constraints balance table h_table
  have partial_balance : ∀ channel ∈ finished, PartialBalancedChannel witness channel := by
    intro channel h_channel
    apply partialBalancedChannel_of_balancedChannel
    exact balance _ <| finished_subset h_channel
  apply spec_and_guarantees_of_soundChannels ?soundChannels ?assumptions ?constraints
    partial_balance table h_table |>.left
  <;> (simp only [circuit_norm]; assumption)

/-- Empty ensemble satisfies SoundChannels -/
theorem empty_soundChannels : (empty F PublicIO).SoundChannels [] := by
  simp only [circuit_norm]

/-- Empty ensemble satisfies TableSoundness -/
theorem empty_tableSoundness : (empty F PublicIO).TableSoundness :=
  tableSoundness_of_soundChannels ⟨ [], List.Subset.refl [], empty_soundChannels ⟩

-- adding one table to a SoundChannels ensemble preserves SoundChannels under some
-- easy-to-prove assumptions on what channels the new table uses
theorem orderedChannels_of_soundChannels_addTable (ens : Ensemble F PublicIO)
  (table : Component F) {finished : List (RawChannel F)} :
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
  simp only [circuit_norm, verifier_empty, allTables] at h_sound ⊢
  -- proof is a trivial combination of the hypotheses
  simp_all

theorem orderedChannels_of_soundChannels_merge (ens1 ens2 : Ensemble F PublicIO)
  {finished : List (RawChannel F)} :
    -- given a sound channels ensemble with empty verifier,
    ens1.SoundChannels finished →
    ens1.verifier = .empty F PublicIO →
    -- assuming that the new tables' channelsWithRequirements contain none of the finished channels
    (∀ channel ∈ finished, channel ∉ ens2.channelsWithRequirements) →
    -- the merged ensemble with the new table satisfies OrderedChannels!
    (ens1.merge ens2).OrderedChannels finished := by
  intro h_sound verifier_empty reqs_disjoint_finished channel h_channel
  simp only [circuit_norm, allTables] at h_sound ⊢
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
  -- TODO get rid of this assumption, by being more flexible about table order
  -- => use "∃ permutation, s.t. ordered" instead of "ordered" in Ensemble.OrderedChannels
  verifier_empty : ensemble.verifier = .empty F PublicIO

attribute [circuit_norm] SoundEnsemble.finished_consistent SoundEnsemble.finished_subset SoundEnsemble.subset_finished
  SoundEnsemble.ordered_channels SoundEnsemble.verifier_empty

namespace SoundEnsemble
lemma soundChannels (ens : SoundEnsemble F PublicIO) : ens.SoundChannels ens.finished := by
  rcases ens with
    ⟨ ens, finished, finished_consistent, finished_subset, subset_finished, ordered_channels, verifier_empty ⟩
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

@[circuit_norm] lemma empty_tables  : (empty F PublicIO).tables = [] := rfl
@[circuit_norm] lemma empty_channels : (empty F PublicIO).channels = [] := rfl
@[circuit_norm] lemma empty_finished : (empty F PublicIO).finished = [] := rfl
@[circuit_norm] lemma empty_verifier : (empty F PublicIO).verifier = .empty F PublicIO := rfl

def addTable (soundEns : SoundEnsemble F PublicIO) (table : Component F)
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

variable {soundEns : SoundEnsemble F PublicIO} {table : Component F}
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

def addChannel (soundEns : SoundEnsemble F PublicIO) (channel : RawChannel F) : SoundEnsemble F PublicIO where
  ensemble := { soundEns.ensemble with channels := channel :: soundEns.channels }
  finished := soundEns.finished
  finished_consistent := soundEns.finished_consistent
  finished_subset := by simp [soundEns.finished_subset]
  subset_finished := soundEns.subset_finished
  ordered_channels := soundEns.ordered_channels
  verifier_empty := soundEns.verifier_empty

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
    have := soundEns.soundChannels_markFinished soundEns.soundChannels channel'
    exact this.right.left channel' (by simp)
  verifier_empty := soundEns.verifier_empty

variable {channel : RawChannel F} [channel.Consistent] {h_mem : channel ∈ soundEns.channels}

@[circuit_norm] lemma markFinished_channels :
  (soundEns.markFinished channel h_mem).channels = soundEns.channels := rfl
@[circuit_norm] lemma markFinished_tables :
  (soundEns.markFinished channel h_mem).tables = soundEns.tables := rfl
@[circuit_norm] lemma markFinished_finished :
  (soundEns.markFinished channel h_mem).finished = channel :: soundEns.finished := rfl

def addFinishedChannel (soundEns : SoundEnsemble F PublicIO) (channel : RawChannel F)
  [channel.Consistent] : SoundEnsemble F PublicIO :=
  soundEns
    |>.addChannel channel
    |>.markFinished channel

@[circuit_norm] lemma addFinishedChannel_channels {channel : RawChannel F} [channel.Consistent] :
  (soundEns.addFinishedChannel channel).channels = channel :: soundEns.channels := rfl
@[circuit_norm] lemma addFinishedChannel_tables {channel : RawChannel F} [channel.Consistent] :
  (soundEns.addFinishedChannel channel).tables = soundEns.tables := rfl
@[circuit_norm] lemma addFinishedChannel_finished {channel : RawChannel F} [channel.Consistent] :
  (soundEns.addFinishedChannel channel).finished = channel :: soundEns.finished := rfl

def toFormal (soundEns : SoundEnsemble F PublicIO)
    (Assumptions Spec : PublicIO F → Prop)
    (assumptionsConsistency : soundEns.AssumptionsConsistency Assumptions)
    (specConsistency : soundEns.SpecConsistency Spec) :
    FormalEnsemble F PublicIO where
  ensemble := soundEns.ensemble
  Assumptions := Assumptions
  Spec := Spec
  soundness := by
    apply soundEns.soundness_of_tableSoundness_and_specConsistency
      Assumptions Spec ?_ assumptionsConsistency specConsistency
    apply soundEns.tableSoundness_of_soundChannels
    use soundEns.finished, soundEns.finished_subset
    exact soundEns.soundChannels
end SoundEnsemble
end Air.Flat
