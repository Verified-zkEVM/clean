module

public import Clean.Air.OrderedChannel

@[expose] public section

/-!
# Offline memory checking

A read-only memory is a verifier-known table that other components read through a channel, like a
static lookup. A lookup table answers repeated reads by counting them in a multiplicity column,
which needs balance by field sums. A memory answers each read with a pull and a push of its own, so
that it is sound under every balance check, including multiset balance in binary fields.

Every entry of the memory carries a counter, a power of a primitive field element `g`. The memory
table seeds each entry with counter `1` and finally pulls it with its last counter, and a read of an
entry with counter `c` pulls it and pushes it back with counter `c * g`. The reads of an entry that
is not in the table could only balance among themselves, closing their counters into a cycle under
multiplication by `g`, which takes `orderOf g` reads: more than there can be interactions.
-/

variable {F : Type} [FiniteField F]

/-- If multiplying a list of nonzero field elements by `g` permutes it, every element's orbit under
`g` lies in it, so a nonempty list has at least `orderOf g` elements. -/
theorem orderOf_le_length_of_perm {g : F} {counters : List F}
    (perm : (counters.map (· * g)).Perm counters) (ne_zero : ∀ c ∈ counters, c ≠ 0)
    {c : F} (mem : c ∈ counters) : orderOf g ≤ counters.length := by
  classical
  have closed : ∀ x ∈ counters, g ^ 1 * x ∈ counters := fun x hx => by
    simpa [mul_comm] using perm.mem_iff.mp (List.mem_map_of_mem hx)
  have orbit : ∀ k : ℕ, g ^ k * c ∈ counters := by
    intro k
    induction k with
    | zero => simpa using mem
    | succ k ih => simpa [pow_succ', mul_assoc] using closed _ ih
  have injOn : Set.InjOn (fun k : ℕ => g ^ k * c) (Finset.range (orderOf g)) := by
    intro i hi j hj h
    simp only [mul_left_inj' (ne_zero c mem)] at h
    exact pow_injOn_Iio_orderOf (by simpa using hi) (by simpa using hj) h
  calc orderOf g = ((Finset.range (orderOf g)).image fun k => g ^ k * c).card := by
        rw [Finset.card_image_of_injOn injOn, Finset.card_range]
    _ ≤ counters.toFinset.card := by
        apply Finset.card_le_card
        intro x hx
        obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hx
        exact List.mem_toFinset.mpr (orbit k)
    _ ≤ counters.length := List.toFinset_card_le counters

namespace Air.Flat.Memory

/-- The interactions of one read: a pull of a message whose last element, its counter, is `c ≠ 0`,
and a push of the same message with counter `c * g`. -/
def IsRead (g : F) (block : List (Interaction F)) : Prop :=
  ∃ pull push : Interaction F, ∃ c : F, block = [pull, push] ∧ c ≠ 0 ∧
    pull.Pull ∧ push.direction = .push ∧ push.mult = 1 ∧
    pull.msg = pull.msg.pop.push c ∧ push.msg = pull.msg.pop.push (c * g)

/-- Interactions whose entry, the message without its counter, is good, or which are inactive or
unit pulls. -/
def IsOther (Good : Array F → Prop) (block : List (Interaction F)) : Prop :=
  ∀ i ∈ block, Good i.msg.pop ∨ i.mult = 0 ∨ i.Pull

lemma length_filter_add_length_filter_le {α : Type} (l : List α) (p q : α → Bool)
    (disjoint : ∀ a ∈ l, p a → q a → False) :
    (l.filter p).length + (l.filter q).length ≤ l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ih := ih fun b hb => disjoint b (List.mem_cons_of_mem a hb)
    have := disjoint a List.mem_cons_self
    by_cases hp : p a <;> by_cases hq : q a <;> simp_all <;> omega

lemma perm_flatMap_append {α β : Type} (l : List α) (f g : α → List β) :
    (l.flatMap fun a => f a ++ g a).Perm (l.flatMap f ++ l.flatMap g) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.flatMap_cons, List.append_assoc]
    refine List.Perm.append_left _ ?_
    exact (ih.append_left (g a)).trans (List.perm_append_comm_assoc _ _ _)

/--
The counting argument of offline memory checking. The interactions on the memory's counter channel
come in blocks, which are reads or other interactions. If they are balanced and fewer than the field
size, every unit pull is of a good entry: the reads of a bad entry can only balance among
themselves, which takes `orderOf g` of them.
-/
theorem good_of_pull {g : F} (h_order : orderOf g = FiniteField.size F - 1)
    (Good : Array F → Prop) (blocks : List (List (Interaction F)))
    (nonempty : ∀ i ∈ blocks.flatten, i.msg.size ≠ 0)
    (balance : BalancedInteractions blocks.flatten)
    (length_lt : blocks.flatten.length < FiniteField.size F)
    (h_blocks : ∀ block ∈ blocks, IsRead g block ∨ IsOther Good block) :
    ∀ i ∈ blocks.flatten, i.Pull → Good i.msg.pop := by
  classical
  intro a a_mem a_pull
  by_contra bad
  set key := a.msg.pop
  -- the counters of the active pushes and pulls of the bad entry
  let counters (direction : Direction) (l : List (Interaction F)) : List F :=
    (l.filter fun i => i.direction = direction ∧ i.mult ≠ 0 ∧ i.msg.pop = key).map (·.msg.back!)
  let reads := blocks.flatMap fun block => if IsRead g block then counters .pull block else []
  let others := blocks.flatMap fun block => if IsRead g block then [] else counters .pull block
  have counters_flatten (direction : Direction) :
      counters direction blocks.flatten = blocks.flatMap (counters direction) := by
    simp [counters, List.filter_flatten, List.map_flatten, List.flatMap]
    rfl
  -- a read pushes its pulled counter times `g`, and other blocks don't push the bad entry
  have counters_push : counters .push blocks.flatten = reads.map (· * g) := by
    rw [counters_flatten, List.map_flatMap]
    apply List.flatMap_congr
    intro block h_block
    split_ifs with h_read
    · obtain ⟨pull, push, c, rfl, -, ⟨h_pull, h_pull_one⟩, h_push, h_one, h_pull_msg, h_push_msg⟩ :=
        h_read
      have h_push_key : push.msg.pop = pull.msg.pop := by rw [h_push_msg, Array.pop_push]
      have h_pull_back : pull.msg.back! = c := by rw [h_pull_msg, Array.back!_push]
      have h_push_back : push.msg.back! = c * g := by rw [h_push_msg, Array.back!_push]
      by_cases h_key : pull.msg.pop = key
      · simp [counters, h_pull, h_pull_one, h_push, h_one, h_push_key, h_key, h_pull_back,
          h_push_back]
      · simp [counters, h_pull, h_push, h_push_key, h_key]
    · simp only [List.map_nil, counters, List.map_eq_nil_iff, List.filter_eq_nil_iff,
        decide_eq_true_eq, not_and]
      intro i h_i h_direction h_mult h_key
      rcases (h_blocks block h_block).resolve_left h_read i h_i with h | h | h
      · exact bad (h_key ▸ h)
      · exact h_mult h
      · simp [h.1] at h_direction
  -- the pulls of the bad entry are those of reads, and those of other blocks
  have counters_pull : (counters .pull blocks.flatten).Perm (reads ++ others) := by
    rw [counters_flatten]
    have : blocks.flatMap (counters .pull) = blocks.flatMap fun block =>
        (if IsRead g block then counters .pull block else []) ++
          (if IsRead g block then [] else counters .pull block) := by
      apply List.flatMap_congr
      intro block _
      split_ifs <;> simp
    rw [this]
    exact perm_flatMap_append _ _ _
  -- counters count the active interactions with the bad entry
  have count_counters (direction : Direction) (x : F) :
      (counters direction blocks.flatten).count x =
        activeCount blocks.flatten direction (key.push x) := by
    simp only [counters, activeCount, List.count_eq_countP, List.countP_map, List.countP_filter]
    apply List.countP_congr
    intro i h_i
    have h_size := nonempty i h_i
    simp only [Function.comp_apply, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨h_x, h_direction, h_mult, h_key⟩
      refine ⟨h_direction, ?_, h_mult⟩
      rw [Array.eq_push_pop_back!_of_size_ne_zero h_size, h_key, h_x]
    · rintro ⟨h_direction, h_msg, h_mult⟩
      exact ⟨by rw [h_msg, Array.back!_push], h_direction, h_mult, by rw [h_msg, Array.pop_push]⟩
  -- the interactions with the bad entry have multiplicity `0` or `1`
  have isBool (x : F) : ∀ i ∈ blocks.flatten, i.msg = key.push x → IsBool i.mult := by
    intro i h_i h_msg
    obtain ⟨block, h_block, h_i⟩ := List.mem_flatten.mp h_i
    rcases h_blocks block h_block with h_read | h_other
    · obtain ⟨pull, push, c, rfl, -, ⟨-, h_pull_one⟩, -, h_one, -⟩ := h_read
      rcases List.mem_pair.mp h_i with rfl | rfl
      · exact .inr h_pull_one
      · exact .inr h_one
    · rcases h_other i h_i with h | h | h
      · rw [h_msg, Array.pop_push] at h
        exact absurd h bad
      · exact .inl h
      · exact .inr h.2
  have perm : (reads.map (· * g)).Perm (reads ++ others) := by
    rw [← counters_push]
    refine List.Perm.trans ?_ counters_pull
    apply List.perm_iff_count.mpr
    intro x
    rw [count_counters, count_counters]
    exact balance.activeCount_push_eq_activeCount_pull_of_isBool _ (isBool x)
  have others_nil : others = [] := by
    have := perm.length_eq
    simp only [List.length_map, List.length_append] at this
    exact List.eq_nil_of_length_eq_zero (by omega)
  rw [others_nil, List.append_nil] at perm counters_pull
  -- the bad entry is read, with nonzero counters
  have a_mem_reads : a.msg.back! ∈ reads := by
    apply counters_pull.mem_iff.mp
    simp only [counters, List.mem_map, List.mem_filter, decide_eq_true_eq]
    exact ⟨a, ⟨a_mem, a_pull.1, by simp [a_pull.2], rfl⟩, rfl⟩
  have reads_ne_zero : ∀ c ∈ reads, c ≠ 0 := by
    intro c h_c
    obtain ⟨block, h_block, h_c⟩ := List.mem_flatMap.mp h_c
    split_ifs at h_c with h_read
    · obtain ⟨pull, push, c', rfl, h_ne, -, h_push, -, h_pull_msg, -⟩ := h_read
      simp only [counters, List.mem_map, List.mem_filter, List.mem_pair, decide_eq_true_eq] at h_c
      obtain ⟨i, ⟨rfl | rfl, h_direction, -⟩, rfl⟩ := h_c
      · rwa [h_pull_msg, Array.back!_push]
      · simp [h_push] at h_direction
    · simp at h_c
  -- a cycle of reads takes `orderOf g` of them, but there are fewer interactions
  have orbit := orderOf_le_length_of_perm perm reads_ne_zero a_mem_reads
  have bound := length_filter_add_length_filter_le blocks.flatten
    (fun i => decide (i.direction = .push ∧ i.mult ≠ 0 ∧ i.msg.pop = key))
    (fun i => decide (i.direction = .pull ∧ i.mult ≠ 0 ∧ i.msg.pop = key))
    (fun i _ h_push h_pull => by simp_all)
  have push_length := congrArg List.length counters_push
  have pull_length := counters_pull.length_eq
  simp only [counters, List.length_map] at push_length pull_length
  have := FiniteField.fieldSize_pos (F := F)
  omega

end Air.Flat.Memory

namespace Air.Flat
variable {Entry : TypeMap} [ProvableType Entry]

/-- A verifier-known read-only memory of `height` entries of type `Entry`, read through a channel.
The reads are checked offline, with counters that are powers of the primitive element
`generator`. -/
structure Memory (F : Type) [FiniteField F] (Entry : TypeMap) [ProvableType Entry] where
  name : String
  height : UInt64
  /-- The entry at index `i`. Fixed rows can't read prover data or hints. -/
  entry (i : Witgen.U64Expr F) : Witgen.M F (Entry (Witgen.FExpr F))
  /-- What it means to be in the memory. Reading an entry from the memory's channel guarantees it. -/
  Contains : Entry F → Prop
  /-- `Contains` holds exactly for the entries of the memory. -/
  contains_iff : ∀ value, Contains value ↔ ∃ i < height, value = (entry .idx).evalRow i
  /-- The factor by which each read advances the counter of its entry. -/
  generator : F
  orderOf_generator : orderOf generator = FiniteField.size F - 1

namespace Memory
variable (memory : Memory F Entry)

/-- The channel through which other components read the memory. -/
def channel : Channel F Entry where
  name := memory.name
  Guarantees entry _ := memory.Contains entry

/-- The channel of the entries with their counters, which only the memory's components use. -/
def counterChannel : Channel F (ProvablePair Entry field) where
  name := memory.name ++ ".counter"
  Guarantees message _ := memory.Contains message.1

@[circuit_norm] lemma channel_name : memory.channel.name = memory.name := rfl
@[circuit_norm] lemma channel_guarantees (entry : Entry F) (data : ProverData F) :
    memory.channel.Guarantees entry data ↔ memory.Contains entry := .rfl
@[circuit_norm] lemma counterChannel_name :
    memory.counterChannel.name = memory.name ++ ".counter" := rfl
@[circuit_norm] lemma counterChannel_guarantees (entry : Entry F) (counter : F)
    (data : ProverData F) :
    memory.counterChannel.Guarantees (entry, counter) data ↔ memory.Contains entry := .rfl

@[circuit_norm] lemma channel_eq_counterChannel_iff :
    memory.channel.toRaw = memory.counterChannel.toRaw ↔ False := by
  simp only [iff_false]
  intro h
  have := congrArg (·.name.length) h
  simp [circuit_norm, String.length_append] at this

@[circuit_norm] lemma counterChannel_eq_channel_iff :
    memory.counterChannel.toRaw = memory.channel.toRaw ↔ False := by
  rw [eq_comm, channel_eq_counterChannel_iff]

/-- One memory row: seeds its entry with counter `1`, and finally pulls it with its last counter. -/
def provider : GeneralFormalCircuit F (ProvablePair Entry field) unit where
  name := memory.name
  main
  | (entry, final) => do
    memory.counterChannel.push (entry, 1)
    memory.counterChannel.pull (entry, final)
  exposedChannels input _ :=
    expose memory.counterChannel [pushed (input.1, 1), pulled input]
  exposedChannels_eq input _ := by
    obtain ⟨entry, final⟩ := input
    simp only [circuit_norm]
  channelsWithRequirements := [memory.counterChannel.toRaw]
  Assumptions input _ := memory.Contains input.1
  ProverAssumptions input _ _ := memory.Contains input.1
  Spec _ _ _ := True
  soundness := by
    circuit_proof_start [counterChannel]
    rw [← h_input] at h_assumptions
    exact h_assumptions
  completeness := by
    circuit_proof_start
    rcases input with ⟨entry, final⟩
    simp_all [counterChannel]

/-- One read: pulls the entry with its counter, which is nonzero, and pushes it with the next
counter. It answers a read on the memory's channel. -/
def reader : GeneralFormalCircuit F (ProvablePair field (ProvablePair Entry field)) unit where
  name := memory.name ++ ".reader"
  main
  | (enabled, (entry, counter)) => do
    assertZero (enabled * (enabled - 1))
    let inverse ← witness counter⁻¹
    assertZero (enabled * (counter * inverse - 1))
    memory.counterChannel.pullIf enabled (entry, counter)
    memory.counterChannel.pushIf enabled (entry, counter * .const memory.generator)
    memory.channel.pushIf enabled entry
  exposedChannels input _ :=
    expose memory.counterChannel [pulledIf input.1 input.2,
      pushedIf input.1 (input.2.1, input.2.2 * .const memory.generator)]
  exposedChannels_eq input _ := by
    obtain ⟨enabled, entry, counter⟩ := input
    simp only [circuit_norm, if_neg (memory.channel_eq_counterChannel_iff.not.mpr not_false)]
  channelsWithRequirements := [memory.counterChannel.toRaw, memory.channel.toRaw]
  ProverAssumptions
  | (enabled, (entry, counter)), _, _ =>
    enabled = 0 ∨ enabled = 1 ∧ memory.Contains entry ∧ counter ≠ 0
  Spec _ _ _ := True
  soundness := by
    circuit_proof_start
    obtain ⟨h_bool, -, h_pull⟩ := h_holds
    rcases mul_eq_zero.mp h_bool with h | h
    · simp [h]
    · rw [sub_eq_zero] at h
      simp [h, h_pull h]
  completeness := by
    circuit_proof_start
    rcases input with ⟨enabled, entry, counter⟩
    simp only [Prod.mk.injEq] at h_input
    rcases h_assumptions with h | ⟨h, h_contains, h_ne⟩ <;> simp_all [mul_inv_cancel₀]

/-- An entry that is in the memory, as the elements of a message without its counter. -/
def Good (entry : Array F) : Prop := ∃ value, memory.Contains value ∧ (toElements value).toArray = entry

omit [FiniteField F] in
lemma toArray_toElements_pair (entry : Entry F) (counter : F) :
    (toElements (M := ProvablePair Entry field) (entry, counter)).toArray =
      (toElements entry).toArray.push counter := by
  simp [ProvableType.toElements]

omit [FiniteField F] in
lemma toArray_toElements_pop (message : ProvablePair Entry field F) :
    (toElements message).toArray.pop = (toElements message.1).toArray := by
  obtain ⟨entry, counter⟩ := message
  rw [toArray_toElements_pair, Array.pop_push]

omit [FiniteField F] in
lemma toArray_toElements_eq_push (message : ProvablePair Entry field F) :
    (toElements message).toArray = (toElements message).toArray.pop.push message.2 := by
  rw [toArray_toElements_pop]
  exact toArray_toElements_pair message.1 message.2

omit [FiniteField F] in
lemma toArray_toElements_fst (message : Vector F (size (ProvablePair Entry field))) :
    (toElements (fromElements (M := ProvablePair Entry field) message).1).toArray =
      message.toArray.pop := by
  conv_rhs => rw [← ProvableType.toElements_fromElements (M := ProvablePair Entry field) message]
  rw [toArray_toElements_pair, Array.pop_push]

variable {memory} in
lemma guarantees_of_good {i : Interaction F} (h_channel : i.channel = memory.counterChannel.toRaw)
    (data : ProverData F) (good : memory.Good i.msg.pop) : i.Guarantees data := by
  obtain ⟨channel, direction, mult, msg, h_size⟩ := i
  subst h_channel
  obtain ⟨value, h_contains, h_value⟩ := good
  intro _ _
  change memory.Contains (fromElements (M := ProvablePair Entry field) ⟨msg, h_size⟩).1
  have h := toArray_toElements_fst (Entry := Entry) ⟨msg, h_size⟩
  rw [← h_value] at h
  have h_eq : (fromElements (M := ProvablePair Entry field) ⟨msg, h_size⟩).1 = value := by
    simpa [ProvableType.fromElements_toElements] using
      congrArg (fromElements (M := Entry)) (Vector.toArray_inj.mp h)
  rw [h_eq]
  exact h_contains

variable {memory} in
lemma good_of_requirements {i : Interaction F} (h_channel : i.channel = memory.counterChannel.toRaw)
    {data : ProverData F} (requirements : i.Requirements data) :
    memory.Good i.msg.pop ∨ i.mult = 0 ∨ i.Pull := by
  obtain ⟨channel, direction, mult, msg, h_size⟩ := i
  subst h_channel
  by_cases h_mult : mult = 0
  · exact .inr (.inl h_mult)
  cases direction
  · exact .inl ⟨_, requirements h_mult, toArray_toElements_fst (Entry := Entry) ⟨msg, h_size⟩⟩
  · exact .inr (.inr ⟨rfl, (requirements : mult = 0 ∨ mult = 1).resolve_left h_mult⟩)

/-- The memory as a component: its fixed entries, followed by the last counter of each. -/
def table : Component F where
  circuit := memory.provider
  -- TODO generate the last counters, see `reader`
  generation := .preallocated {
    channel := memory.counterChannel
    trigger := .push
    height := memory.height
    input i := do
      let entry ← memory.entry i
      return (fromElements ((toElements entry).map .fixed), .witness (.const 1))
  }
  circuit_assumptions_of_assumptions := by
    rintro i ⟨value, final⟩ data ⟨hi, hfixed⟩ - -
    refine (memory.contains_iff value).mpr ⟨i, hi, ?_⟩
    simp only [WitnessGeneration.PreallocatedMode.FixedAt, Witgen.M.bind_def, Witgen.M.pure_def,
      toElements, Vector.toList_append, Vector.toList_map, ProvableType.toElements_fromElements,
      List.forall₂_iff_get] at hfixed
    have h : toElements value = toElements ((memory.entry .idx).evalRow i) := by
      ext j hj
      simpa [List.getElem_append_left, hj, Witgen.M.evalRow, Witgen.eval,
        WitnessGeneration.Cell.FixedMatches, ProvableType.toElements_fromElements, circuit_norm]
        using hfixed.2 j (by simp; omega) (by simp; omega)
    simpa [ProvableType.fromElements_toElements] using congrArg (fromElements (M := Entry)) h

/-- The reads as a component: one row per read on the memory's channel. Padding rows are
disabled. -/
def readerComponent : Component F where
  circuit := memory.reader
  -- TODO generate the counters of reads, the number of earlier reads of the same entry
  generation := .demand {
    channel := memory.channel
    trigger := .pull
    input entry :=
      pure (1, (fromElements (M := Entry) ((toElements (M := Entry) entry).map (.witness ∘ .expr)), 1))
  }

omit [ProvableType Entry] in
lemma eval_fst {α β : TypeMap} [ProvableType α] [ProvableType β] (env : Environment F)
    (pair : ProvablePair α β (Expression F)) :
    eval env pair.1 = (eval env pair : ProvablePair α β F).1 := by
  obtain ⟨a, b⟩ := pair
  rw [eval_pair]

omit [ProvableType Entry] in
lemma eval_snd {α β : TypeMap} [ProvableType α] [ProvableType β] (env : Environment F)
    (pair : ProvablePair α β (Expression F)) :
    eval env pair.2 = (eval env pair : ProvablePair α β F).2 := by
  obtain ⟨a, b⟩ := pair
  rw [eval_pair]

lemma table_interactionValuesWith (env : Environment F) :
    memory.table.operations.interactionValuesWith memory.counterChannel.toRaw env =
      [memory.counterChannel.pushedValue ((memory.table.rowInput env).1, 1),
        memory.counterChannel.pulledValue (memory.table.rowInput env)] := by
  rw [Operations.interactionValuesWith_eq_map,
    Component.interactionsWith_of_exposedChannels (table := memory.table) (List.mem_singleton_self _)]
  simp only [List.map_cons, List.map_nil, Component.rowInput, ← eval_varFromOffset_valueFromOffset]
  refine congrArg₂ (· :: ·) (Channel.eval_pushed.trans ?_) (congrArg (· :: []) Channel.eval_pulled)
  simp only [circuit_norm]
  have := eval_fst env (varFromOffset (ProvablePair Entry field) 0)
  congr 4

/-- The interactions of a row of the reads on the counter channel: a read, or disabled. -/
lemma reader_block {env : Environment F}
    (h : memory.readerComponent.operations.ConstraintsHold env) :
    let block := memory.readerComponent.operations.interactionValuesWith
      memory.counterChannel.toRaw env
    IsRead memory.generator block ∨ IsOther memory.Good block := by
  rw [Component.constraintsHold_iff] at h
  simp only [Operations.interactionValuesWith_eq_map,
    Component.interactionsWith_of_exposedChannels (table := memory.readerComponent)
      (List.mem_singleton_self _)]
  simp only [circuit_norm, readerComponent, reader] at h ⊢
  simp only [Channel.eval_toRaw_pulledIf, Channel.eval_toRaw_pushedIf, eval_pair]
  obtain ⟨h_bool, h_inverse⟩ := h
  rcases mul_eq_zero.mp h_bool with h_zero | h_one
  · right
    intro i h_i
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h_i
    rcases h_i with rfl | rfl <;> simp [Channel.pulledIfValue, Channel.pushedIfValue, h_zero]
  · left
    rw [sub_eq_zero] at h_one
    rw [h_one, one_mul, sub_eq_zero] at h_inverse
    have h_entry := eval_fst env
      (varFromOffset (ProvablePair field (ProvablePair Entry field)) (F := F) 0).2
    have h_counter := eval_snd env
      (varFromOffset (ProvablePair field (ProvablePair Entry field)) (F := F) 0).2
    refine ⟨_, _, _, rfl, ?_, ⟨rfl, h_one⟩, rfl, h_one, toArray_toElements_eq_push _, ?_⟩
    · exact fun h_zero => left_ne_zero_of_mul_eq_one h_inverse
        ((ProvableType.eval_field _ _).symm.trans (h_counter.trans h_zero))
    · simp only [Channel.pulledIfValue, Channel.pushedIfValue, toArray_toElements_pair,
        toArray_toElements_pop]
      congr 2
      · exact congrArg toElements h_entry
      · rw [ProvableType.eval_field]
        simp only [Expression.eval]
        exact congrArg (· * memory.generator)
          ((ProvableType.eval_field _ _).symm.trans h_counter)

/-- The interactions of a memory row on the counter channel are of its entry. -/
lemma table_block {env : Environment F} (h : memory.Contains (memory.table.rowInput env).1) :
    IsOther memory.Good
      (memory.table.operations.interactionValuesWith memory.counterChannel.toRaw env) := by
  rw [table_interactionValuesWith]
  intro i h_i
  left
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h_i
  rcases h_i with rfl | rfl
  · exact ⟨_, h, by simp [Channel.pushedValue, toArray_toElements_pair]⟩
  · exact ⟨_, h, (toArray_toElements_pop (Entry := Entry) (memory.table.rowInput env)).symm⟩

variable {memory} in
/--
Soundness of offline memory checking: in a witness where all components other than the memory's
satisfy their requirements on its counter channel, every read is of an entry of the memory.
-/
theorem guarantees_of_balanced {balance : Balance F} [balance.LengthLtSize]
    {PublicIO : TypeMap} [ProvableType PublicIO] {ens : Ensemble F PublicIO}
    (witness : EnsembleWitness ens) (assumptions : witness.Assumptions)
    (constraints : witness.Constraints)
    (balanced : balance.Balanced
      (witness.interactionsWith memory.counterChannel.toRaw))
    (requirements : ∀ table ∈ witness.tables,
      table.component ∉ [memory.table, memory.readerComponent] →
        table.ChannelRequirements memory.counterChannel.toRaw)
    (verifier_requirements : ens.VerifierChannelRequirements witness.publicInput witness.data
      memory.counterChannel.toRaw) :
    ∀ i ∈ witness.interactionsWith memory.counterChannel.toRaw, i.Guarantees witness.data := by
  set channel := memory.counterChannel.toRaw
  -- the interactions on the counter channel, cut into the verifier's and those of each row
  let blocks : List (List (Interaction F)) := witness.verifierInteractionsWith channel ::
    witness.tables.flatMap fun table => table.table.map fun row =>
      table.component.operations.interactionValuesWith channel (table.environment row)
  have h_flatten : blocks.flatten = witness.interactionsWith channel := by
    simp [blocks, EnsembleWitness.interactionsWith, Tables.interactionsWith,
      EnsembleWitness.toTables, Table.interactionsWith]
    simp only [List.flatMap]
    rw [List.flatten_flatten]
    simp [Function.comp_def]
  have h_channel (i) (h_i : i ∈ witness.interactionsWith channel) : i.channel = channel :=
    witness.channel_eq_of_mem_interactionsWith h_i
  have good := good_of_pull memory.orderOf_generator memory.Good blocks
    (by
      rw [h_flatten]
      intro i h_i
      rw [i.same_size, h_channel i h_i]
      simp [channel, circuit_norm])
    (h_flatten ▸ balance.balancedInteractions_of_balanced _ balanced)
    (h_flatten ▸ Balance.LengthLtSize.length_lt_size _ balanced)
    (by
      intro block h_block
      simp only [blocks, List.mem_cons, List.mem_flatMap, List.mem_map] at h_block
      rcases h_block with rfl | ⟨table, h_table, row, h_row, rfl⟩
      · right
        rw [witness.verifierChannelRequirements_iff_forall] at verifier_requirements
        intro i h_i
        exact good_of_requirements (h_channel i (witness.mem_interactionsWith.mpr (.inl h_i)))
          (verifier_requirements i h_i)
      have h_mem : ∀ i ∈ table.component.operations.interactionValuesWith channel
          (table.environment row), i ∈ table.interactionsWith channel :=
        fun i h_i => List.mem_flatMap.mpr ⟨row, h_row, h_i⟩
      by_cases h_provider : table.component = memory.table
      · right
        have h_contains :=
          table.circuitAssumptions_of_assumptions (assumptions table h_table) row h_row
        rw [h_provider] at h_contains ⊢
        exact memory.table_block h_contains
      by_cases h_reader : table.component = memory.readerComponent
      · have h_constraints := constraints table h_table row h_row
        rw [h_reader] at h_constraints ⊢
        exact memory.reader_block h_constraints
      right
      have reqs := requirements table h_table (by simp [h_provider, h_reader])
      rw [Table.channelRequirements_iff_forall] at reqs
      intro i h_i
      exact good_of_requirements
        (h_channel i (witness.mem_interactionsWith.mpr (.inr ⟨table, h_table, h_mem i h_i⟩)))
        (witness.same_data table h_table ▸ reqs i (h_mem i h_i)))
  intro i h_i
  by_cases h_pull : i.Pull
  · exact guarantees_of_good (h_channel i h_i) _ (good i (h_flatten ▸ h_i) h_pull)
  · exact RawChannel.Normal.guarantees_of_not_pull i _ (h_channel i h_i) h_pull

/-- The memory's counter channel, closed by offline memory checking. -/
def closedChannel (balance : Balance F) [balance.LengthLtSize] : ClosedChannel F balance where
  channel := memory.counterChannel.toRaw
  owners := [memory.table, memory.readerComponent]
  guarantees_of_balanced := guarantees_of_balanced

@[circuit_norm] lemma table_name : memory.table.circuit.name = memory.name := rfl
@[circuit_norm] lemma readerComponent_name :
    memory.readerComponent.circuit.name = memory.name ++ ".reader" := rfl
@[circuit_norm] lemma table_channelsWithGuarantees :
    memory.table.circuit.channelsWithGuarantees = [memory.counterChannel.toRaw] := rfl
@[circuit_norm] lemma table_channelsWithRequirements :
    memory.table.circuit.channelsWithRequirements = [memory.counterChannel.toRaw] := rfl
@[circuit_norm] lemma readerComponent_channelsWithGuarantees :
    memory.readerComponent.circuit.channelsWithGuarantees = [memory.counterChannel.toRaw] := rfl
@[circuit_norm] lemma readerComponent_channelsWithRequirements :
    memory.readerComponent.circuit.channelsWithRequirements =
      [memory.counterChannel.toRaw, memory.channel.toRaw] := rfl
@[circuit_norm] lemma table_assumptions (input : memory.table.Input F) (data : ProverData F) :
    memory.table.Assumptions input data = True := rfl
@[circuit_norm] lemma readerComponent_assumptions (input : memory.readerComponent.Input F)
    (data : ProverData F) : memory.readerComponent.Assumptions input data = True := rfl
@[circuit_norm] lemma closedChannel_channel (balance : Balance F) [balance.LengthLtSize] :
    (memory.closedChannel balance).channel = memory.counterChannel.toRaw := rfl
@[circuit_norm] lemma closedChannel_owners (balance : Balance F) [balance.LengthLtSize] :
    (memory.closedChannel balance).owners = [memory.table, memory.readerComponent] := rfl

end Memory

namespace SoundEnsemble
variable {PublicIO : TypeMap} [ProvableType PublicIO] {balance : Balance F}

/-- Add a memory: its components, its counter channel, which is closed, and its channel, which is
finished right away. -/
def addMemory (soundEns : SoundEnsemble F PublicIO balance) [balance.LengthLtSize]
    (memory : Memory F Entry)
    (names : ([memory.table, memory.readerComponent] ++ soundEns.tables).map
      (·.circuit.name) |>.Nodup := by simp [circuit_norm])
    (fresh_channel : memory.name ∉ soundEns.channels.map (·.name) := by simp [circuit_norm])
    (fresh_counter : memory.name ++ ".counter" ∉ soundEns.channels.map (·.name)
      := by simp [circuit_norm]) :
    SoundEnsemble F PublicIO balance :=
  have not_mem {channel : RawChannel F} (h : channel.name ∉ soundEns.channels.map (·.name)) :
      channel ∉ soundEns.channels := fun h_mem => h (List.mem_map_of_mem h_mem)
  have channel_not_mem : memory.channel.toRaw ∉ soundEns.channels := not_mem fresh_channel
  have counter_not_mem : memory.counterChannel.toRaw ∉ soundEns.channels := not_mem fresh_counter
  have channel_not_finished : memory.channel.toRaw ∉ soundEns.finished :=
    fun h => channel_not_mem (soundEns.finished_subset h)
  soundEns.addChannel memory.channel.toRaw fresh_channel
    |>.addClosedChannel (memory.closedChannel balance)
      (by
        show memory.counterChannel.name ∉ (memory.channel.toRaw :: soundEns.channels).map (·.name)
        simp only [List.map_cons, List.mem_cons, not_or]
        refine ⟨fun h => ?_, fresh_counter⟩
        have := congrArg String.length h
        simp [circuit_norm, String.length_append] at this)
      (by
        intro owner h_owner
        simp only [Memory.closedChannel_owners, List.mem_cons, List.not_mem_nil, or_false]
          at h_owner
        rcases h_owner with rfl | rfl <;> simp [circuit_norm])
      (by
        intro owner h_owner channel h_channel
        simp only [Memory.closedChannel_owners, List.mem_cons, List.not_mem_nil, or_false]
          at h_owner
        rcases h_owner with rfl | rfl <;>
          simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_false] at h_channel
        · exact .inl h_channel
        · rcases h_channel with rfl | rfl
          · exact .inl rfl
          · exact .inr ⟨List.mem_cons_self .., channel_not_finished⟩)
      names
    |>.markFinished memory.channel.toRaw
      (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      (by
        show memory.channel.toRaw ∉ memory.counterChannel.toRaw :: soundEns.closed.map (·.channel)
        simp only [List.mem_cons, not_or, Memory.channel_eq_counterChannel_iff, not_false_eq_true,
          true_and]
        exact fun h => channel_not_mem (soundEns.closed_subset h))

variable {soundEns : SoundEnsemble F PublicIO balance} [balance.LengthLtSize]
  {memory : Memory F Entry} {names fresh_channel fresh_counter}

@[circuit_norm] lemma addMemory_tables :
    (soundEns.addMemory memory names fresh_channel fresh_counter).tables =
      memory.table :: memory.readerComponent :: soundEns.tables := rfl
@[circuit_norm] lemma addMemory_channels :
    (soundEns.addMemory memory names fresh_channel fresh_counter).channels =
      memory.counterChannel.toRaw :: memory.channel.toRaw :: soundEns.channels := rfl
@[circuit_norm] lemma addMemory_ordered :
    (soundEns.addMemory memory names fresh_channel fresh_counter).ordered =
      memory.channel.toRaw :: soundEns.ordered := rfl
@[circuit_norm] lemma addMemory_closed :
    (soundEns.addMemory memory names fresh_channel fresh_counter).closed =
      memory.closedChannel balance :: soundEns.closed := rfl
@[circuit_norm] lemma addMemory_verifier :
    (soundEns.addMemory memory names fresh_channel fresh_counter).verifier =
      soundEns.verifier := rfl

end SoundEnsemble
end Air.Flat
