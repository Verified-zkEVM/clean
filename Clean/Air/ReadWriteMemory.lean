module

public import Clean.Air.Lookup

@[expose] public section

/-!
# Read-write memory

A read-write memory is a range of addresses whose values change over time. Its records
`(address, value, time)` live on a memory channel: every access pulls the current record of its
address and pushes a new one, at a later time. A memory table, with one row per address, pushes the
verifier-known initial record of each address that is accessed, at time `0`, and pulls its last
record.

The memory channel guarantees nothing. What the accesses read follows from a global argument, see
`Clean.Air.MemoryVm`: when the accesses happen in the steps of a VM, and their times are the clocks
of these steps, balance of the memory channel replays them in the order in which the VM executes,
so every read returns the last value written to its address.

Times are field elements, compared by their `val`. Every access checks that its time and the gap to
the previous time are less than `timeBound`, through a range lookup. Since `2 * timeBound ≤ p`, the
two add up without wrapping around, so the previous time is earlier, once it is known to be less
than `timeBound`. The global argument shows that for every pulled record.

Witness generation reads what the accesses pull from the prover's private input: the hint holds the
previous record of the access at every time, and the last record of every address.
-/

namespace Air.Flat
variable {p : ℕ} [Fact p.Prime]

/-- The value of an address, written at a time. -/
structure MemoryRecord (F : Type) where
  address : F
  value : F
  time : F
deriving ProvableStruct

/-- A read-write memory of `size` addresses, with verifier-known initial values, whose accesses
happen at times less than `timeBound`. -/
structure ReadWriteMemory (p : ℕ) [Fact p.Prime] where
  name : String
  size : UInt64
  /-- The initial value at an address, as a witness program of the address. -/
  initial (address : Witgen.U64Expr (F p)) : Witgen.FExpr (F p)
  timeBound : UInt64
  /-- Distinct addresses are distinct field elements. -/
  size_le : size.toNat ≤ p
  /-- A time and a time gap add up without wrapping around. -/
  timeBound_le : 2 * timeBound.toNat ≤ p

namespace ReadWriteMemory
variable (memory : ReadWriteMemory p)

/-- The initial value at an address. -/
def initialValue (address : ℕ) : F p :=
  (memory.initial .idx).eval
    (WitnessGeneration.inputContext [] (WitnessGeneration.rowEnvironment (.empty (F p))) address)

/-- The initial contents of the memory. -/
def initialMemory (address : F p) : F p := memory.initialValue address.val

/-- What an access shows about the record it pulls: its own time is less than `timeBound`, and the
pulled record was written earlier, if its time is less than `timeBound` too. -/
def Ordered (previousTime time : F p) : Prop :=
  time.val < memory.timeBound.toNat ∧
    (previousTime.val < memory.timeBound.toNat → previousTime.val < time.val)

/-- The channel of memory records. -/
def channel : Channel (F p) MemoryRecord where
  name := memory.name
  Guarantees _ _ := True

@[circuit_norm] lemma channel_name : memory.channel.name = memory.name := rfl
@[circuit_norm] lemma channel_guarantees (record : MemoryRecord (F p)) (data : ProverData (F p)) :
    memory.channel.Guarantees record data ↔ True := .rfl

/-- The times `0, ..., timeBound - 1`, for range checks of times and time gaps. -/
def range : Lookup (F p) field where
  name := memory.name ++ " times"
  height := memory.timeBound
  row i := pure i.toField
  rowOf time := time.val
  Contains time := time.val < memory.timeBound.toNat
  contains_iff time := by
    have := memory.timeBound_le
    simp only [circuit_norm, Nat.mod_eq_of_lt (UInt64.toNat_lt _)]
    constructor
    · intro h
      have h64 : time.val < 2 ^ 64 := h.trans (UInt64.toNat_lt _)
      refine ⟨time.val.toUInt64, ?_, ?_⟩
      · simp [h]
      · simp
    · rintro ⟨i, hi, rfl⟩
      rwa [ZMod.val_cast_of_lt (by omega)]

/-- An access whose time and time gap are less than `timeBound` follows the record it pulls, if
that record's time is less than `timeBound`. -/
theorem ordered_of_range {previousTime time : F p} (h_time : time.val < memory.timeBound.toNat)
    (h_gap : (time - previousTime - 1).val < memory.timeBound.toNat) :
    memory.Ordered previousTime time := by
  refine ⟨h_time, fun h_previous => ?_⟩
  have := memory.timeBound_le
  set gap := time - previousTime - 1
  have h_sum : time = previousTime + gap + 1 := by simp only [gap]; ring
  have h_add : (previousTime + gap).val = previousTime.val + gap.val :=
    ZMod.val_add_of_lt (by omega)
  have h_add_one : (previousTime + gap + 1).val = previousTime.val + gap.val + 1 := by
    rw [ZMod.val_add_of_lt (by rw [ZMod.val_one]; omega), h_add, ZMod.val_one]
  rw [h_sum, h_add_one]
  omega

/-- The name of the hint table holding the previous record of the access at every time. -/
def previousKey : String := memory.name ++ " previous"

/-- The name of the hint table holding the last record of every address. -/
def finalKey : String := memory.name ++ " final"

/-- The prover's private input that witness generation of the memory reads: for every time, the
value and time of the record that the access at this time pulls, and for every address, the value
and time of its last record. -/
abbrev ProverInput := fields (2 * memory.timeBound.toNat + 2 * memory.size.toNat)

/-- The hint tables of `ProverInput`. -/
def hintTables : List HintTable := [
  { key := memory.previousKey, width := 2, offset := 0, rows := memory.timeBound.toNat },
  { key := memory.finalKey, width := 2, offset := 2 * memory.timeBound.toNat,
    rows := memory.size.toNat } ]

/-- The prover's private input for a list of accesses in time order: the records they push. -/
def proverInput (accesses : List (MemoryRecord (F p))) : memory.ProverInput (F p) :=
  let initial := (Array.range memory.size.toNat).map fun address =>
    (memory.initialValue address, (0 : F p))
  let (previous, final) := accesses.foldl (fun (previous, current) access =>
      (previous.set! access.time.val (current[access.address.val]?.getD (0, 0)),
        current.set! access.address.val (access.value, access.time)))
    (Array.replicate memory.timeBound.toNat (0, 0), initial)
  let cells := (previous ++ final).flatMap fun (value, time) => #[value, time]
  Vector.ofFn fun i => cells[i.val]?.getD 0

/-- The hint cell of `column` at the access time `time`: the previous value (`0`) or time (`1`). -/
def previousCell (time : Expression (F p)) (column : Fin 2) : Witgen.FExpr (F p) :=
  .hintGet memory.previousKey 2 time.val column

/-- The hint cell that `previousCell` reads. -/
def previousCellIn (hint : ProverHint (F p)) (time : F p) (column : Fin 2) : F p :=
  ((hint memory.previousKey 2)[(UInt64.ofNat time.val).toNat]?.getD default)[column]

/-- The range checks of an access at `time`, whose previous record has time `previousTime`. -/
def InRange (previousTime time : F p) : Prop :=
  time.val < memory.timeBound.toNat ∧ (time - previousTime - 1).val < memory.timeBound.toNat

/-! ### The memory table -/

/-- A row of the memory table: an address, its initial value, and its last record, which the row
consumes if `multiplicity` is `1`. -/
structure MemoryCell (F : Type) where
  address : F
  initialValue : F
  finalValue : F
  finalTime : F
  multiplicity : F
deriving ProvableStruct

/-- One row of the memory table: if enabled, it provides the initial record of its address, at time
`0`, and consumes its last record. -/
def cell : GeneralFormalCircuit (F p) MemoryCell unit where
  name := memory.name
  main input := do
    assertZero (input.multiplicity * (input.multiplicity - 1))
    memory.channel.pullIf input.multiplicity
      { address := input.address, value := input.finalValue, time := input.finalTime }
    memory.channel.pushIf input.multiplicity
      { address := input.address, value := input.initialValue, time := 0 }
  exposedChannels
  | { address, initialValue, finalValue, finalTime, multiplicity }, _ =>
    expose memory.channel [
      pulledIf multiplicity { address, value := finalValue, time := finalTime },
      pushedIf multiplicity { address, value := initialValue, time := 0 } ]
  ProverAssumptions input _ _ := input.multiplicity = 0 ∨ input.multiplicity = 1
  Spec _ _ _ := True
  requirementsChannelsLawful input offset := by
    simp only [circuit_norm, channel]
    intro env h_bool
    rcases mul_eq_zero.mp h_bool with h | h <;> simp_all [sub_eq_zero]
  soundness := by
    circuit_proof_start [channel]
    rcases mul_eq_zero.mp h_holds with h | h <;> simp_all [sub_eq_zero]
  completeness := by
    circuit_proof_start
    rcases h_assumptions with h | h <;> simp [h]

/-- The memory table: one row per address, whose fixed cells are the address and its initial
value. Witness generation counts the first access of an address in its row's multiplicity, and reads
the address's last record from the hint. -/
def component : Component (F p) where
  circuit := memory.cell
  generation := .preallocated {
    channel := memory.channel
    trigger := .pull
    height := memory.size
    input i := pure {
      address := .fixed i.toField
      initialValue := .fixed (memory.initial i)
      finalValue := .witness (.hintGet memory.finalKey 2 i 0)
      finalTime := .witness (.hintGet memory.finalKey 2 i 1)
      multiplicity := .multiplicity }
    rowOf record := record.address.val
  }

@[circuit_norm] lemma component_name : memory.component.circuit.name = memory.name := rfl
@[circuit_norm] lemma component_assumptions (input : memory.component.Input (F p))
    (data : ProverData (F p)) :
    memory.component.Assumptions input data = True := rfl
@[circuit_norm] lemma component_channelsWithGuarantees :
    memory.component.circuit.channelsWithGuarantees = [memory.channel.toRaw] := rfl
@[circuit_norm] lemma component_channelsWithRequirements :
    memory.component.circuit.channelsWithRequirements = [] := rfl

/-- A row of the memory table pulls the last record of its address and pushes its initial record,
if enabled. -/
lemma component_interactionValuesWith (env : Environment (F p)) :
    memory.component.operations.interactionValuesWith memory.channel.toRaw env =
      let cell := memory.component.rowInput env
      [memory.channel.pulledIfValue cell.multiplicity
          { address := cell.address, value := cell.finalValue, time := cell.finalTime },
        memory.channel.pushedIfValue cell.multiplicity
          { address := cell.address, value := cell.initialValue, time := 0 }] := by
  have h_cell (input : Var MemoryCell (F p)) (n : ℕ) :
      ((memory.cell.main input).operations n).interactionValuesWith memory.channel.toRaw env =
        let cell := eval env input
        [memory.channel.pulledIfValue cell.multiplicity
            { address := cell.address, value := cell.finalValue, time := cell.finalTime },
          memory.channel.pushedIfValue cell.multiplicity
            { address := cell.address, value := cell.initialValue, time := 0 }] := by
    obtain ⟨address, initialValue, finalValue, finalTime, multiplicity⟩ := input
    rw [Operations.interactionValuesWith_eq_map,
      memory.cell.exposedChannels_eq _ n _ (List.mem_singleton_self _)]
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true]
    refine ⟨(Channel.eval_pulledIf (channel := memory.channel)).trans ?_,
      (Channel.eval_pushedIf (channel := memory.channel)).trans ?_⟩ <;> simp [circuit_norm]
  rw [Operations.interactionValuesWith_eq_map, Component.interactionsWith_eq,
    ← Operations.interactionValuesWith_eq_map, Component.rowInput,
    ← eval_varFromOffset_valueFromOffset]
  exact h_cell _ _

/-- The multiplicity of a row of the memory table is `0` or `1`. -/
lemma component_isBool {env : Environment (F p)}
    (h : memory.component.operations.ConstraintsHold env) :
    IsBool (memory.component.rowInput env).multiplicity := by
  have h_cell (input : Var MemoryCell (F p)) (n : ℕ) :
      ((memory.cell.main input).operations n).ConstraintsHold env →
        IsBool (eval env input).multiplicity := by
    obtain ⟨address, initialValue, finalValue, finalTime, multiplicity⟩ := input
    simp only [circuit_norm, cell]
    intro h_bool
    rcases mul_eq_zero.mp h_bool with h | h
    · exact .inl h
    · exact .inr (sub_eq_zero.mp h)
  rw [Component.constraintsHold_iff] at h
  rw [Component.rowInput, ← eval_varFromOffset_valueFromOffset]
  exact h_cell _ _ h

/-- Row `i` of the memory table holds address `i` and its initial value. -/
lemma component_fixedRowsMatch {rows : List (Array (F p))}
    (h : memory.component.FixedRowsMatch rows) :
    rows.length = memory.size.toNat ∧ ∀ i (hi : i < rows.length) (data : ProverData (F p)),
      (memory.component.rowInput (.fromArray rows[i] data)).address = i ∧
      (memory.component.rowInput (.fromArray rows[i] data)).initialValue =
        memory.initialValue i := by
  simp only [Component.FixedRowsMatch, component] at h
  refine ⟨h.1, fun i hi data => ?_⟩
  have h_fixed := h.2 i hi
  have h_i : i < 2 ^ 64 := h.1 ▸ hi |>.trans (UInt64.toNat_lt _)
  have h_elements {α : Type} (cell : MemoryCell α) : (toElements cell).toList =
      [cell.address, cell.initialValue, cell.finalValue, cell.finalTime, cell.multiplicity] := by
    simp only [ProvableStruct.toList_toElements]
    rfl
  simp only [WitnessGeneration.PreallocatedMode.FixedAt, Witgen.M.pure_def] at h_fixed
  erw [h_elements, h_elements] at h_fixed
  simp only [List.forall₂_cons, List.Forall₂.nil, and_true] at h_fixed
  obtain ⟨h_address, h_initial, -⟩ := h_fixed
  simp only [WitnessGeneration.Cell.FixedMatches, UInt64.toNat_ofNat_of_lt' h_i]
    at h_address h_initial
  refine ⟨h_address.trans ?_, h_initial⟩
  simp [circuit_norm, WitnessGeneration.inputContext]

/-! ### Accesses -/

structure ReadInput (F : Type) where
  enabled : F
  address : F
  time : F
deriving ProvableStruct

/-- Read an address at a time, if enabled: pull its current record, and push it back at `time`.
Returns the pulled record, whose value is the value read. -/
def read : GeneralFormalCircuit (F p) ReadInput MemoryRecord where
  name := memory.name ++ " read"
  main input := do
    assertZero (input.enabled * (input.enabled - 1))
    let value ← witness (memory.previousCell input.time 0)
    let previousTime ← witness (memory.previousCell input.time 1)
    memory.range.channel.pullIf input.enabled input.time
    memory.range.channel.pullIf input.enabled (input.time - previousTime - 1)
    memory.channel.pullIf input.enabled { address := input.address, value, time := previousTime }
    memory.channel.pushIf input.enabled { address := input.address, value, time := input.time }
    return { address := input.address, value, time := previousTime }
  exposedChannels input i₀ :=
    let previous : Var MemoryRecord (F p) :=
      { address := input.address, value := var ⟨i₀⟩, time := var ⟨i₀ + 1⟩ }
    expose memory.channel [
      pulledIf input.enabled previous, pushedIf input.enabled { previous with time := input.time } ]
  ProverAssumptions input _ hint := input.enabled = 0 ∨
    input.enabled = 1 ∧ memory.InRange (memory.previousCellIn hint input.time 1) input.time
  Spec input previous _ := input.enabled = 1 →
    previous.address = input.address ∧ memory.Ordered previous.time input.time
  requirementsChannelsLawful input offset := by
    obtain ⟨enabled, address, time⟩ := input
    simp only [circuit_norm, channel, range]
    intro env h_bool
    rcases mul_eq_zero.mp h_bool with h | h <;> simp_all [sub_eq_zero]
  soundness := by
    circuit_proof_start [channel, range]
    obtain ⟨h_bool, h_time, h_gap⟩ := h_holds
    rcases mul_eq_zero.mp h_bool with h | h <;> simp_all [sub_eq_zero]
    exact memory.ordered_of_range h_time h_gap
  completeness := by
    circuit_proof_start [range, previousCell, previousCellIn, InRange]
    rcases h_assumptions with h | ⟨h, h_range⟩ <;> simp_all

structure WriteInput (F : Type) where
  enabled : F
  address : F
  value : F
  time : F
deriving ProvableStruct

/-- Write a value to an address at a time, if enabled: pull its current record, and push the new
value at `time`. Returns the pulled record. -/
def write : GeneralFormalCircuit (F p) WriteInput MemoryRecord where
  name := memory.name ++ " write"
  main input := do
    assertZero (input.enabled * (input.enabled - 1))
    let previousValue ← witness (memory.previousCell input.time 0)
    let previousTime ← witness (memory.previousCell input.time 1)
    memory.range.channel.pullIf input.enabled input.time
    memory.range.channel.pullIf input.enabled (input.time - previousTime - 1)
    memory.channel.pullIf input.enabled
      { address := input.address, value := previousValue, time := previousTime }
    memory.channel.pushIf input.enabled
      { address := input.address, value := input.value, time := input.time }
    return { address := input.address, value := previousValue, time := previousTime }
  exposedChannels input i₀ :=
    expose memory.channel [
      pulledIf input.enabled { address := input.address, value := var ⟨i₀⟩, time := var ⟨i₀ + 1⟩ },
      pushedIf input.enabled
        { address := input.address, value := input.value, time := input.time } ]
  ProverAssumptions input _ hint := input.enabled = 0 ∨
    input.enabled = 1 ∧ memory.InRange (memory.previousCellIn hint input.time 1) input.time
  Spec input previous _ := input.enabled = 1 →
    previous.address = input.address ∧ memory.Ordered previous.time input.time
  requirementsChannelsLawful input offset := by
    obtain ⟨enabled, address, value, time⟩ := input
    simp only [circuit_norm, channel, range]
    intro env h_bool
    rcases mul_eq_zero.mp h_bool with h | h <;> simp_all [sub_eq_zero]
  soundness := by
    circuit_proof_start [channel, range]
    obtain ⟨h_bool, h_time, h_gap⟩ := h_holds
    rcases mul_eq_zero.mp h_bool with h | h <;> simp_all [sub_eq_zero]
    exact memory.ordered_of_range h_time h_gap
  completeness := by
    circuit_proof_start [range, previousCell, previousCellIn, InRange]
    rcases h_assumptions with h | ⟨h, h_range⟩ <;> simp_all

section
variable {data : ProverData (F p)} {hint : ProverHint (F p)}

@[circuit_norm] lemma read_output (input : Var ReadInput (F p)) (n : ℕ) :
    memory.read.output input n =
      { address := input.address, value := var ⟨n⟩, time := var ⟨n + 1⟩ } := rfl
@[circuit_norm] lemma read_localLength (input : Var ReadInput (F p)) :
    memory.read.localLength input = 2 := rfl
@[circuit_norm] lemma read_channelsWithGuarantees : memory.read.channelsWithGuarantees =
    [memory.range.channel.toRaw, memory.range.channel.toRaw, memory.channel.toRaw] := rfl
@[circuit_norm] lemma read_channelsWithRequirements :
    memory.read.channelsWithRequirements = [] := rfl
@[circuit_norm] lemma read_assumptions (input : ReadInput (F p)) :
    memory.read.Assumptions input data = True := rfl
@[circuit_norm] lemma read_spec (input : ReadInput (F p)) (previous : MemoryRecord (F p)) :
    memory.read.Spec input previous data = (input.enabled = 1 →
      previous.address = input.address ∧ memory.Ordered previous.time input.time) := rfl
@[circuit_norm] lemma read_proverAssumptions (input : ReadInput (F p)) :
    memory.read.ProverAssumptions input data hint = (input.enabled = 0 ∨
      input.enabled = 1 ∧ memory.InRange (memory.previousCellIn hint input.time 1) input.time) :=
  rfl

@[circuit_norm] lemma write_output (input : Var WriteInput (F p)) (n : ℕ) :
    memory.write.output input n =
      { address := input.address, value := var ⟨n⟩, time := var ⟨n + 1⟩ } := rfl
@[circuit_norm] lemma write_localLength (input : Var WriteInput (F p)) :
    memory.write.localLength input = 2 := rfl
@[circuit_norm] lemma write_channelsWithGuarantees : memory.write.channelsWithGuarantees =
    [memory.range.channel.toRaw, memory.range.channel.toRaw, memory.channel.toRaw] := rfl
@[circuit_norm] lemma write_channelsWithRequirements :
    memory.write.channelsWithRequirements = [] := rfl
@[circuit_norm] lemma write_assumptions (input : WriteInput (F p)) :
    memory.write.Assumptions input data = True := rfl
@[circuit_norm] lemma write_spec (input : WriteInput (F p)) (previous : MemoryRecord (F p)) :
    memory.write.Spec input previous data = (input.enabled = 1 →
      previous.address = input.address ∧ memory.Ordered previous.time input.time) := rfl
@[circuit_norm] lemma write_proverAssumptions (input : WriteInput (F p)) :
    memory.write.ProverAssumptions input data hint = (input.enabled = 0 ∨
      input.enabled = 1 ∧ memory.InRange (memory.previousCellIn hint input.time 1) input.time) :=
  rfl
end

open Classical in
/-- The memory interactions of a read, which pulls the previous record and pushes it back. -/
@[circuit_norm]
theorem read_interactions (input : Var ReadInput (F p)) (n : ℕ) :
    (FlatOperation.interactions (memory.read.toSubcircuit n input).ops.toFlat).filter
        (fun i => i.channel = memory.channel.toRaw) = [
      (memory.channel.pulledIf input.enabled
        { address := input.address, value := var ⟨n⟩, time := var ⟨n + 1⟩ }).toRaw,
      (memory.channel.pushedIf input.enabled
        { address := input.address, value := var ⟨n⟩, time := input.time }).toRaw ] :=
  memory.read.toSubcircuit_interactions_filter_of_mem_exposedChannels (List.mem_singleton_self _)

open Classical in
/-- The memory interactions of a write, which pulls the previous record and pushes the new one. -/
@[circuit_norm]
theorem write_interactions (input : Var WriteInput (F p)) (n : ℕ) :
    (FlatOperation.interactions (memory.write.toSubcircuit n input).ops.toFlat).filter
        (fun i => i.channel = memory.channel.toRaw) = [
      (memory.channel.pulledIf input.enabled
        { address := input.address, value := var ⟨n⟩, time := var ⟨n + 1⟩ }).toRaw,
      (memory.channel.pushedIf input.enabled
        { address := input.address, value := input.value, time := input.time }).toRaw ] :=
  memory.write.toSubcircuit_interactions_filter_of_mem_exposedChannels (List.mem_singleton_self _)

end ReadWriteMemory
end Air.Flat
