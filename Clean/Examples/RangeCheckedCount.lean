module

public import Clean.Air.CountedChannel
public import Clean.Air.Lookup
public import Clean.Air.OrderedChannel
public import Clean.Air.StagedChannels

@[expose] public section

/-!
# A count range-checked on another channel

`CountedSquares` constrains its count arithmetically, which only scales to a small bound. Here a
row needs a fact up to `255` times, pulls it once with that multiplicity, and range-checks the
multiplicity by pulling it from a byte table. The requirement the counted pull owes,
`count = 0 ∨ CountUpTo 255 count`, then follows from the row's guarantee on `bytes`, not from its
constraints.

`OrderedChannel` cannot order this ensemble: the consumer both pulls from `doubles` and owes
requirements on it, which `OrderedChannelRefl` rules out. A finishing order of channels can:
`tableSoundness` finishes `bytes` before `doubles` through
`Ensemble.tableSoundness_of_stagedRequirements`. Witness generation is not exercised; each
component declares one only because `Component` requires it.
-/

namespace RangeCheckedCount

open Air.Flat

variable {p : ℕ} [Fact p.Prime] [Fact (p > 512)]

/-- The bytes `0, ..., 255`, for range checks. -/
def bytes : Lookup (F p) field where
  name := "bytes"
  height := 256
  row i := pure i
  rowOf value := value.val
  Contains value := value.val < 256
  contains_iff value := by
    simp only [circuit_norm, Nat.mod_eq_of_lt (UInt64.toNat_lt _)]
    constructor
    · intro h
      refine ⟨value.val.toUInt64, ?_, ?_⟩ <;> simp [h]
    · rintro ⟨i, hi, rfl⟩
      rwa [ZMod.val_cast_of_lt (by linarith [(‹Fact (p > 512)›).out])]

/-- Pairs `(x, y)` with `y = x + x`. -/
def doubles : Channel (F p) (ProvablePair field field) where
  name := "doubles"
  Guarantees | (x, y), _ => y = x + x

omit [Fact (p > 512)] in
/-- A byte is `0` or a count up to `255`: the step from the byte table's guarantee to the
requirement of a counted pull. -/
lemma eq_zero_or_countUpTo_of_val_lt {count : F p} (h : count.val < 256) :
    count = 0 ∨ CountUpTo 255 count := by
  by_cases h0 : count = 0
  · exact .inl h0
  · exact .inr (countUpTo_of_ne_zero_of_val_le h0 (by omega))

lemma bytes_ne_doubles : (bytes (p := p)).channel.toRaw ≠ doubles.counted 255 := fun h => by
  have := congrArg RawChannel.name h
  simp [bytes, doubles, circuit_norm] at this

structure DoublerInput (F : Type) where
  x : F
  y : F
  /-- how many pulls this row answers, counted with multiplicity -/
  mult : F
deriving ProvableStruct

/-- The doubling chip: constrains `y = x + x`, which every active push of the pair owes. -/
def doubler : GeneralFormalCircuit (F p) DoublerInput unit where
  name := "doubler"
  main input := do
    input.y === input.x + input.x
    doubles.emitUpTo 255 input.mult (input.x, input.y)
  channelsWithRequirements := [doubles.counted 255]
  Spec _ _ _ := True
  ProverAssumptions input _ _ := input.y = input.x + input.x
  soundness := by
    circuit_proof_start [doubles]
    simp_all
  completeness := by
    circuit_proof_start [doubles]
    simp_all

/-- One row per distinct pair pulled from `doubles`, its multiplicity the total pulled count. -/
abbrev doublerComponent : Component (F p) where
  circuit := doubler
  generation := .demand {
    trigger := .pull
    channel := doubles
    input | (x, y) => pure { x, y, mult := .multiplicity }
  }

structure ConsumerInput (F : Type) where
  x : F
  y : F
  /-- how many times this row needs the fact -/
  count : F
deriving ProvableStruct

/-- A row that needs `y = x + x` up to `255` times and pulls it once with that multiplicity, which
only its pull from `bytes` bounds. -/
def consumer : GeneralFormalCircuit (F p) ConsumerInput unit where
  name := "consumer"
  main input := do
    bytes.channel.pull input.count
    doubles.pullUpTo 255 input.count (input.x, input.y)
  channelsWithRequirements := [doubles.counted 255]
  Spec input _ _ := input.count ≠ 0 → input.y = input.x + input.x
  ProverAssumptions input _ _ := input.count.val < 256 ∧ input.y = input.x + input.x
  soundness := by
    circuit_proof_start [bytes, doubles]
    obtain ⟨h_byte, h_double⟩ := h_holds
    have h_count := eq_zero_or_countUpTo_of_val_lt h_byte
    refine ⟨fun h0 => ?_, h_count⟩
    rcases h_count with h | h
    · exact absurd h h0
    · exact h_double h
  completeness := by
    circuit_proof_start [bytes, doubles]
    simp_all

/-- One consumer row per pair pushed to `doubles` that nothing has pulled. -/
abbrev consumerComponent : Component (F p) where
  circuit := consumer
  generation := .demand {
    trigger := .push
    channel := doubles
    input | (x, y) => pure { x, y, count := .witness 1 }
  }

/-- `OrderedChannel` cannot take the consumer: it pulls from `doubles` and owes on it. -/
example :
    ¬ OrderedChannelRefl (doubles.counted 255 : RawChannel (F p)) (consumerComponent (p := p)) := by
  simp [circuit_norm, consumer]

/-- The consumer's requirement on `doubles`, from its guarantee on `bytes` alone. Neither
`Component.requirementsAfter_of_not_mem` nor `Component.requirementsAfter_of_guarantees_subset`
gives it: the consumer owes on `doubles` and has guarantees on it. -/
theorem consumer_requirementsAfter : (consumerComponent (p := p)).RequirementsAfter
    (doubles.counted 255) [bytes.channel.toRaw] := by
  rintro table h_comp - - guarantees row h_row
  have h_bytes := guarantees _ List.mem_cons_self row h_row
  rw [h_comp] at h_bytes ⊢
  simp only [Component.interactions_eq, Component.rowOperations, circuit_norm, consumer]
    at h_bytes ⊢
  exact eq_zero_or_countUpTo_of_val_lt h_bytes.1

/-- The ensemble: the byte table, the doubling chip, and the consumer. -/
def ensemble : Ensemble (F p) unit where
  tables := [consumerComponent, doublerComponent, bytes.component]
  unique_names := by simp [circuit_norm, consumer, doubler, bytes]
  channels := [doubles.counted 255, bytes.channel.toRaw]
  unique_channel_names := by simp [circuit_norm, bytes, doubles]
  tables_channels := by simp [circuit_norm, consumer, doubler, bytes]
  verifier_channels := by simp [circuit_norm]

/-- Every table is sound under `Balance.logUpUpTo 255`, with `bytes` finished before `doubles`. -/
theorem tableSoundness : (ensemble (p := p)).TableSoundness (Balance.logUpUpTo 255) := by
  apply Ensemble.tableSoundness_of_stagedRequirements [doubles.counted 255, bytes.channel.toRaw]
    (List.Subset.refl _)
    (verifier_subset_finished := by simp [ensemble, circuit_norm, Verifier.Program.empty])
    (verifier_staged := Ensemble.verifierStagedRequirementsOn_of_verifier_empty rfl _)
  · simp [ensemble, circuit_norm, consumer, doubler, bytes]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨inferInstance, inferInstance⟩
  · simp only [ensemble, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      circuit_norm]
    refine ⟨⟨consumer_requirementsAfter, Component.requirementsAfter_of_not_mem _
        (by simp [circuit_norm, consumer, bytes_ne_doubles])⟩,
      ⟨Component.requirementsAfter_of_guarantees_subset (by simp [circuit_norm, doubler]),
        Component.requirementsAfter_of_not_mem _
          (by simp [circuit_norm, doubler, bytes_ne_doubles])⟩,
      ⟨Component.requirementsAfter_of_not_mem _ (by simp [circuit_norm, bytes_ne_doubles.symm]),
        Component.requirementsAfter_of_guarantees_subset (by simp [circuit_norm])⟩⟩

end RangeCheckedCount
