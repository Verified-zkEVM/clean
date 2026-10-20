module

public import Clean.Air.Vm
public import Clean.Air.Lookup
public import Clean.Air.WitnessGeneration
public import Clean.Examples.FemtoCairo.FemtoCairo

@[expose] public section

namespace Examples.FemtoCairo.FlatAir

open Air.Flat
open Types
open Spec

variable {p : ℕ} [Fact p.Prime] [p_large_enough : Fact (p > 512)]

instance (p : ℕ) [p_large_enough : Fact (p > 512)] : Fact (ringChar (F p) ≠ 2) :=
  .mk <| by
    simp [F, ZMod.ringChar_zmod_n]
    linarith [p_large_enough.out]

structure ProviderInput F where
  address : F
  value : F
  multiplicity : F
deriving ProvableStruct

def memory (data : ProverData (F p)) : Array (F p) :=
  (data.getRows "memory" ProviderInput).map (·.value)

def MemoryCompletenessAssumption (data : ProverData (F p)) : Prop :=
  let mem := data.getRows "memory" ProviderInput
  mem.size > 0 ∧ mem.size ≤ 2^64 ∧
    ∀ (address : F p) (ha : address.val < mem.size), mem[address.val].address = address

/-- The program, as a table of `(address, value)` rows. -/
def programLookup (program : Array (F p)) (h_program : ValidProgram program) :
    Lookup (F p) fieldPair where
  name := "program"
  height := program.size.toUInt64
  row i := pure (i, program[i])
  Contains
  | (address, value) => ∃ h : address.val < program.size, value = program[address.val]
  contains_iff value := by
    obtain ⟨address, v⟩ := value
    have h_size := h_program.size_lt
    have h_size_u64 := h_program.size_lt_u64
    simp only [circuit_norm, Nat.mod_eq_of_lt (UInt64.toNat_lt _), Nat.mod_eq_of_lt h_size_u64]
    constructor
    · rintro ⟨h, rfl⟩
      refine ⟨address.val.toUInt64, ?_, ?_⟩ <;> simp [h]
    · rintro ⟨i, hi, h⟩
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hval : (i.toNat : F p).val = i.toNat := ZMod.val_cast_of_lt (by omega)
      simp [hval, hi]

def fetchInstruction
    (program : Array (F p)) (h_program : ValidProgram program) :
    GeneralFormalCircuit (F p) field RawInstruction where
  main pc := do
    let rawInstrType ← witness program[pc.val]
    let op1 ← witness program[pc.val + 1]
    let op2 ← witness program[pc.val + 2]
    let op3 ← witness program[pc.val + 3]
    (programLookup program h_program).channel.pull (pc, rawInstrType)
    (programLookup program h_program).channel.pull (pc + 1, op1)
    (programLookup program h_program).channel.pull (pc + 2, op2)
    (programLookup program h_program).channel.pull (pc + 3, op3)
    return { rawInstrType, op1, op2, op3 }

  ProverAssumptions
  | pc, _, _ => pc.val + 3 < program.size

  Spec
  | pc, output, _ =>
      match Spec.fetchInstruction program pc with
      | some claimedOutput => output = claimedOutput
      | none => False

  soundness := by
    circuit_proof_start [programLookup, Spec.fetchInstruction, Spec.memoryAccess]
    split
    case h_2 x h_eq => grind
    case h_1 rawInstrType claimedInstruction instruction h_eq =>
      simp_all only [circuit_norm, explicit_provable_type]
      grind

  completeness := by
    circuit_proof_start [programLookup]
    have h_pc_bound := h_assumptions
    have h_size := h_program.size_lt
    have h_programSize_u64 := h_program.size_lt_u64
    have val_3 : ZMod.val (3 : F p) = 3 := ZMod.val_natCast_of_lt (by linarith)
    have val_2 : ZMod.val (2 : F p) = 2 := ZMod.val_natCast_of_lt (by linarith)
    have val_1 : ZMod.val (1 : F p) = 1 := ZMod.val_one p
    have : input.val < program.size := by linarith
    have : input.val + 1 < program.size := by linarith
    have : input.val + 2 < program.size := by linarith
    have h_no_wrap : input.val + 3 < 2^64 := by omega
    change F p at input
    have : (input + 1).val = input.val + 1 := by field_to_nat
    have : (input + 2).val = input.val + 2 := by field_to_nat
    have : (input + 3).val = input.val + 3 := by field_to_nat
    simp_all

def memoryChannel : Channel (F p) MemoryEntry where
  name := "memory"
  Guarantees entry data :=
    let table := data.getRows "memory" ProviderInput
    ∃ ha : entry.address.val < table.size,
      entry.address = table[entry.address.val].address ∧
      entry.value = table[entry.address.val].value

def readFromMemory : GeneralFormalCircuit (F p) MemoryReadInput field where
  main := fun input => do
    let state := input.state
    let offset := input.offset
    let mode := input.mode
    let addr1 <==
      mode.isDoubleAddressing * (state.ap + offset) +
      mode.isApRelative * (state.ap + offset) +
      mode.isFpRelative * (state.fp + offset)
    let value1 ← witness (Witgen.dataGet "memory" ProviderInput addr1.val).value
    let addr2 <== mode.isDoubleAddressing * value1
    let value2 ← witness (Witgen.dataGet "memory" ProviderInput addr2.val).value
    memoryChannel.pull { address := addr1, value := value1 }
    memoryChannel.pull { address := addr2, value := value2 }
    let value <==
      mode.isDoubleAddressing * value2 +
      mode.isApRelative * value1 +
      mode.isFpRelative * value1 +
      mode.isImmediate * offset
    return value

  ProverAssumptions
  | { state, offset, mode }, data, _ =>
      mode.isEncodedCorrectly ∧
      MemoryCompletenessAssumption data ∧
      (Spec.dataMemoryAccess (memory data) offset mode.val state.ap state.fp).isSome

  Assumptions
  | { mode, .. }, _ => mode.isEncodedCorrectly

  Spec
  | { state, offset, mode }, output, data =>
      match Spec.dataMemoryAccess (memory data) offset mode.val state.ap state.fp with
      | some value => output = value
      | none => False

  soundness := by
    circuit_proof_start [memoryChannel, Spec.dataMemoryAccess, Spec.memoryAccess,
      DecodedAddressingMode.val, DecodedAddressingMode.isEncodedCorrectly, MemoryReadInput.mk.injEq]
    obtain ⟨isDoubleAddressing, isApRelative, isFpRelative, isImmediate⟩ := input_mode
    obtain ⟨_pc, ap, fp⟩ := input_state
    simp only [circuit_norm, explicit_provable_type, State.mk.injEq,
      DecodedAddressingMode.mk.injEq] at h_holds h_assumptions h_input
    obtain ⟨⟨-, rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl⟩ := h_input
    obtain ⟨h_addr1, h_addr2, ⟨h_lt1, -, h_value1⟩, ⟨h_lt2, -, h_value2⟩, h_value⟩ := h_holds
    -- the two memory lookups, as reads of the memory array
    have h_read1 : (memory env.data)[(env.get i₀).val]? = some (env.get (i₀ + 1)) := by
      rw [memory, Array.getElem?_map, Array.getElem?_eq_getElem h_lt1, Option.map_some, h_value1]
    have h_read2 :
        (memory env.data)[(env.get (i₀ + 1 + 1)).val]? = some (env.get (i₀ + 1 + 1 + 1)) := by
      rw [memory, Array.getElem?_map, Array.getElem?_eq_getElem h_lt2, Option.map_some, h_value2]
    clear h_lt1 h_value1 h_lt2 h_value2
    rcases h_assumptions with h_mode | h_mode | h_mode | h_mode <;> simp_all

  completeness := by
    circuit_proof_start [memoryChannel, DecodedAddressingMode.isEncodedCorrectly,
      Spec.dataMemoryAccess, memory, MemoryReadInput.mk.injEq]
    set addr1 := env.get i₀
    set value1 := env.get (i₀ + 1)
    set addr2 := env.get (i₀ + 2)
    set value2 := env.get (i₀ + 3)
    set value := env.get (i₀ + 4)
    set memoryTable := env.data.getRows "memory" ProviderInput with h_memory_table_def
    obtain ⟨addr1_def, value1_def, addr2_def, value2_def, value_def⟩ := h_env
    use addr1_def, addr2_def
    simp only [value_def]
    obtain ⟨isDoubleAddressing, isApRelative, isFpRelative, isImmediate⟩ := input_mode
    obtain ⟨_pc, ap, fp⟩ := input_state
    simp only [circuit_norm, explicit_provable_type, DecodedAddressingMode.mk.injEq,
      State.mk.injEq] at h_input
    simp only [h_input, DecodedAddressingMode.val, Spec.memoryAccess,
      MemoryCompletenessAssumption] at h_assumptions addr1_def addr2_def ⊢
    obtain ⟨h_mode_encode, ⟨h_pos, h_size_le, h_mem_completeness⟩, h_mem_access⟩ := h_assumptions
    have h_size_le' : memoryTable.size ≤ 2^64 := h_size_le
    suffices h_goal : addr1.val < memoryTable.size ∧ addr2.val < memoryTable.size by
      obtain ⟨h_addr1_lt, h_addr2_lt⟩ := h_goal
      constructor
      · use h_addr1_lt
        use h_mem_completeness addr1 h_addr1_lt |>.symm
        change value1 = memoryTable[addr1.val].value
        rw [value1_def]
        simp [h_addr1_lt]
      · constructor
        · change ∃ h : addr2.val < memoryTable.size,
            addr2 = memoryTable[addr2.val].address ∧
            value2 = memoryTable[addr2.val].value
          use h_addr2_lt
          use h_mem_completeness addr2 h_addr2_lt |>.symm
          rw [value2_def]
          simp [h_addr2_lt]
        · simp [value1, value2]
    rcases h_mode_encode with h_mode | h_mode | h_mode | h_mode
    <;> simp only [h_mode, one_mul, zero_mul, add_zero, zero_add, reduceIte] at *
    · have h1 : (ap + input_offset).val < memoryTable.size := by
        by_contra h
        simp [Array.getElem?_eq_none (Nat.le_of_not_lt h)] at h_mem_access
      rw [Array.getElem?_map, Array.getElem?_eq_getElem h1] at h_mem_access
      have h2 : memoryTable[(ap + input_offset).val].value.val < memoryTable.size := by
        by_contra h
        simp [Array.getElem?_eq_none (Nat.le_of_not_lt h)] at h_mem_access
      have h_addr1 : addr1.val < memoryTable.size := addr1_def ▸ h1
      refine ⟨h_addr1, ?_⟩
      rw [addr2_def, value1_def, Nat.mod_eq_of_lt (by omega), Array.getElem?_eq_getElem h_addr1]
      simpa [addr1_def] using h2
    all_goals simp at h_mem_access
    all_goals first
      | exact ⟨addr1_def ▸ h_mem_access, by simpa [addr2_def] using h_pos⟩
      | exact ⟨by simpa [addr1_def] using h_pos, by simpa [addr2_def] using h_pos⟩

def femtoCairoStepMain (program : Array (F p)) (h_program : ValidProgram program)
    (state : Var State (F p)) :
    Circuit (F p) (Var State (F p)) := do
  let raw ← fetchInstruction program h_program state.pc
  let decoded ← decodeInstruction raw.rawInstrType
  let v1 ← readFromMemory { state, offset := raw.op1, mode := decoded.mode1 }
  let v2 ← readFromMemory { state, offset := raw.op2, mode := decoded.mode2 }
  let v3 ← readFromMemory { state, offset := raw.op3, mode := decoded.mode3 }
  nextState { state, decoded, v1, v2, v3 }

@[reducible]
instance (program : Array (F p)) (h_program : ValidProgram program) :
    ElaboratedCircuit (F p) State State (femtoCairoStepMain program h_program) := by
  elaborate_circuit

def femtoCairoStepSpec (program : Array (F p))
    (state nextState : State (F p)) (data : ProverData (F p)) : Prop :=
  Spec.femtoCairoMachineTransition program (memory data) state = some nextState

def femtoCairoStepAssumptions (program : Array (F p))
    (state : State (F p)) (data : ProverData (F p)) (_hint : ProverHint (F p)) : Prop :=
  MemoryCompletenessAssumption data ∧
  (Spec.femtoCairoMachineTransition program (memory data) state).isSome

theorem femtoCairoStepSoundness (program : Array (F p)) (h_program : ValidProgram program) :
    GeneralFormalCircuit.Soundness (F p) (femtoCairoStepMain program h_program)
      (fun _ _ => True) (femtoCairoStepSpec program) := by
  circuit_proof_start [femtoCairoStepSpec, femtoCairoStepAssumptions, femtoCairoStepMain,
    Spec.femtoCairoMachineTransition, fetchInstruction, readFromMemory,
    nextState, decodeInstruction,
    decodeInstructionSpec, Gadgets.toBits]
  obtain ⟨pc_var, ap_var, fp_var⟩ := input_var
  obtain ⟨pc, ap, fp⟩ := input
  simp only [circuit_norm, explicit_provable_type, State.mk.injEq] at h_input
  obtain ⟨h_input_pc, h_input_ap, h_input_fp⟩ := h_input
  obtain ⟨c_fetch, c_decode, c_read1, c_read2, c_read3, c_next⟩ := h_holds
  split at c_fetch
  case h_2 => contradiction
  case h_1 raw_instruction h_eq =>
    rw [h_input_pc] at h_eq
    rw [h_eq, ← c_fetch]
    simp only [Option.bind_eq_bind, Option.bind_some]
    split at c_decode
    case h_2 => contradiction
    case h_1 instr_type mode1 mode2 mode3 h_eq_decode =>
      simp only [circuit_norm, explicit_provable_type] at h_eq_decode ⊢
      simp only [h_eq_decode, Option.bind_some]
      obtain ⟨h_instr_type_val, h_instr_type_encoded_correctly, h_mode1_val,
        h_mode1_encoded_correctly, h_mode2_val, h_mode2_encoded_correctly,
        h_mode3_val, h_mode3_encoded_correctly⟩ := c_decode
      specialize c_read1 h_mode1_encoded_correctly
      rw [h_mode1_val] at c_read1
      specialize c_read2 h_mode2_encoded_correctly
      rw [h_mode2_val] at c_read2
      specialize c_read3 h_mode3_encoded_correctly
      rw [h_mode3_val] at c_read3
      specialize c_next h_instr_type_encoded_correctly
      rw [h_instr_type_val] at c_next
      simp only [circuit_norm, explicit_provable_type] at c_read1 c_read2 c_read3 c_next
      split at c_read1
      case h_2 => contradiction
      case h_1 v1 h_eq_v1 =>
        rw [h_eq_v1, ← c_read1]
        split at c_read2
        case h_2 => contradiction
        case h_1 v2 h_eq_v2 =>
          rw [h_eq_v2, ← c_read2]
          split at c_read3
          case h_2 => contradiction
          case h_1 v3 h_eq_v3 =>
            rw [h_eq_v3, ← c_read3]
            simp only [Option.bind_some]
            split at c_next
            case h_2 => contradiction
            case h_1 next_state h_eq_next => rw [h_eq_next, ← c_next]

theorem femtoCairoStepCompleteness (program : Array (F p)) (h_program : ValidProgram program) :
    GeneralFormalCircuit.Completeness (F p) (femtoCairoStepMain program h_program)
      (femtoCairoStepAssumptions program) (fun _ _ _ => True) := by
  circuit_proof_start [femtoCairoStepAssumptions, femtoCairoStepMain,
    fetchInstruction, decodeInstruction, readFromMemory,
    nextState, Gadgets.toBits]
  obtain ⟨h_memory_completeness, h_transition_isSome⟩ := h_assumptions
  have h_decompose := Spec.transition_isSome_implies_computeNextState_isSome
    program (memory env.data) input h_transition_isSome
  obtain ⟨raw, decode, v1, v2, v3, h_fetch, h_decode, h_v1, h_v2, h_v3,
    h_computeNext⟩ := h_decompose
  have h_fetch_isSome : (Spec.fetchInstruction program input.pc).isSome :=
    Spec.transition_isSome_implies_fetch_isSome program (memory env.data) input h_transition_isSome
  have h_pc_bound : input.pc.val + 3 < program.size :=
    Spec.fetchInstruction_isSome_implies_pc_bound program h_program input.pc h_fetch_isSome
  have h_instr_bound : raw.rawInstrType.val < 256 := by
    have h_decode_bound := Spec.decodeInstruction_isSome_implies_bound raw.rawInstrType
    simp only [Option.isSome_iff_exists] at h_decode_bound
    exact h_decode_bound ⟨decode, h_decode⟩
  let fetched := varFromOffset (F := F p) RawInstruction i₀
  rcases raw with ⟨rawInstrType, op1, op2, op3⟩
  simp only at *
  obtain ⟨h_fetch_env, h_decode_env, h_read1_env, h_read2_env, h_read3_env,
    h_next_env⟩ := h_env
  have h_eval_pc : Expression.eval env input_var.pc = input.pc := by
    rw [← State.eval_pc env input_var, h_input]
  simp only [h_eval_pc] at h_fetch_env
  specialize h_fetch_env h_pc_bound
  simp only [h_fetch, circuit_norm, explicit_provable_type, RawInstruction.mk.injEq] at h_fetch_env
  obtain ⟨h_rawInstrType, h_op1, h_op2, h_op3⟩ := h_fetch_env
  specialize h_decode_env (by rw [h_rawInstrType]; exact h_instr_bound)
  simp only [decodeInstructionSpec, h_rawInstrType, h_decode] at h_decode_env
  obtain ⟨h_instr_type_val, h_instr_type_encoded_correctly, h_mode1_val,
    h_mode1_encoded_correctly, h_mode2_val, h_mode2_encoded_correctly,
    h_mode3_val, h_mode3_encoded_correctly⟩ := h_decode_env
  have h_read1_value := h_read1_env (by
    exact ⟨h_mode1_encoded_correctly, h_memory_completeness, by
      rw [h_op1, h_mode1_val]
      exact Option.isSome_iff_exists.mpr ⟨v1, h_v1⟩⟩) h_mode1_encoded_correctly
  simp only [h_op1, h_mode1_val, h_v1] at h_read1_value
  have h_read2_value := h_read2_env (by
    exact ⟨h_mode2_encoded_correctly, h_memory_completeness, by
      rw [h_op2, h_mode2_val]
      exact Option.isSome_iff_exists.mpr ⟨v2, h_v2⟩⟩) h_mode2_encoded_correctly
  simp only [h_op2, h_mode2_val, h_v2] at h_read2_value
  have h_read3_value := h_read3_env (by
    exact ⟨h_mode3_encoded_correctly, h_memory_completeness, by
      rw [h_op3, h_mode3_val]
      exact Option.isSome_iff_exists.mpr ⟨v3, h_v3⟩⟩) h_mode3_encoded_correctly
  simp only [h_op3, h_mode3_val, h_v3] at h_read3_value
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h_eval_pc]; exact h_pc_bound
  · rw [h_rawInstrType]; exact h_instr_bound
  · exact ⟨h_mode1_encoded_correctly, h_memory_completeness, by
      rw [h_op1, h_mode1_val]
      exact Option.isSome_iff_exists.mpr ⟨v1, h_v1⟩⟩
  · exact ⟨h_mode2_encoded_correctly, h_memory_completeness, by
      rw [h_op2, h_mode2_val]
      exact Option.isSome_iff_exists.mpr ⟨v2, h_v2⟩⟩
  · exact ⟨h_mode3_encoded_correctly, h_memory_completeness, by
      rw [h_op3, h_mode3_val]
      exact Option.isSome_iff_exists.mpr ⟨v3, h_v3⟩⟩
  · exact ⟨h_instr_type_encoded_correctly, by
      rw [h_instr_type_val, h_read1_value, h_read2_value, h_read3_value]
      exact h_computeNext⟩

def femtoCairoStep (program : Array (F p)) (h_program : ValidProgram program) :
    GeneralFormalCircuit (F p) State State where
  main := femtoCairoStepMain program h_program
  ProverAssumptions := femtoCairoStepAssumptions program
  Spec := femtoCairoStepSpec program
  soundness := femtoCairoStepSoundness program h_program
  completeness := femtoCairoStepCompleteness program h_program

def provideMemory : GeneralFormalCircuit (F p) ProviderInput unit where
  name := "memory"
  main | { address, value, multiplicity } => do
    memoryChannel.emit multiplicity { address, value }
  Assumptions
  | { address, value, .. }, data => memoryChannel.Guarantees { address, value } data
  ProverAssumptions
  | { address, value, .. }, data, _ => memoryChannel.Guarantees { address, value } data
  Spec _ _ _ := True
  channelsWithRequirements := [memoryChannel.toRaw]
  soundness := by
    circuit_proof_start [memoryChannel]
    intro _ _
    exact h_assumptions
  completeness := by circuit_proof_start

def memoryFixedColumns (memorySize : UInt64) : FixedColumns (F p) where
  Row := field
  height := memorySize
  row i := pure i

/-- Name of the hint table holding the prover's memory values, one per address. -/
def memoryValuesKey : String := "memoryValues"

/-- One memory row per address, whose value the prover supplies as a hint. Its multiplicity counts
the reads of that address. -/
def memoryComponent (memorySize : UInt64) (h_memorySize : memorySize.toNat < p) :
    Component (F p) where
  circuit := provideMemory
  fixedColumns := some (memoryFixedColumns memorySize)
  circuit_assumptions_of_assumptions := by
    rintro i ⟨address, value, multiplicity⟩ data hfixed hdata -
    simp [memoryFixedColumns, Witgen.RowProgram.width, provideMemory, circuit_norm,
      explicit_provable_type] at hfixed hdata
    obtain ⟨hi, rfl⟩ := hfixed
    have hval : (i.toNat : F p).val = i.toNat := ZMod.val_cast_of_lt (by omega)
    obtain ⟨hsize, hentry⟩ := Array.getElem?_eq_some_iff.mp hdata
    simp [provideMemory, memoryChannel, hval, hsize, hentry]
  generation := .preallocated {
    Row := field
    row i := pure (.hintGet memoryValuesKey 1 i 0)
    counters := [fun row => row.multiplicity]
  }

def stateChannel (program : Array (F p))
    (initialState : State (F p)) : Channel (F p) State where
  name := "state"
  Guarantees state data := ∃ steps,
    Spec.femtoCairoMachineBoundedExecution program (memory data) (some initialState) steps =
      some state

structure ExecutionInput (F : Type) where
  enabled : F
  state : State F
deriving ProvableStruct

/-- One execution row: when enabled, it pulls a state and pushes the state after it. Disabled rows
pad the execution table. -/
def executeStep (program : Array (F p)) (h_program : ValidProgram program)
    (initialState : State (F p)) :
    GeneralFormalCircuit (F p) ExecutionInput unit where
  name := "execution"
  main input := do
    -- has to be inline, channels with requirements proof doesn't handle subcircuits
    assertZero (input.enabled * (input.enabled - 1))
    (stateChannel program initialState).pullIf input.enabled input.state
    let nextState ← femtoCairoStep program h_program input.state
    (stateChannel program initialState).pushIf input.enabled nextState

  exposedChannels input i₀ :=
    let nextState := (femtoCairoStep program h_program).output input.state i₀
    expose (stateChannel program initialState)
      [pulledIf input.enabled input.state, pushedIf input.enabled nextState]
  exposedChannels_eq input i₀ := by
    simp [circuit_norm, femtoCairoStep, stateChannel]

  ProverAssumptions input data hint :=
    (input.enabled = 0 ∨
      input.enabled = 1 ∧ (stateChannel program initialState).Guarantees input.state data) ∧
    (femtoCairoStep program h_program).ProverAssumptions input.state data hint

  Spec _ _ _ := True
  channelsWithRequirements := [(stateChannel program initialState).toRaw]

  soundness := by
    circuit_proof_start [stateChannel, femtoCairoStep, femtoCairoStepSpec,
      Spec.femtoCairoMachineBoundedExecution]
    obtain ⟨h_bool, h_pull, h_step⟩ := h_holds
    rw [mul_eq_zero, sub_eq_zero] at h_bool
    rcases h_bool with rfl | rfl
    · simp
    obtain ⟨steps, hsteps⟩ := h_pull rfl
    refine ⟨by simp, fun _ _ => ⟨steps + 1, ?_⟩⟩
    simp only [Spec.femtoCairoMachineBoundedExecution, hsteps]
    exact h_step

  completeness := by
    circuit_proof_start [stateChannel, femtoCairoStep]
    obtain ⟨rfl | ⟨rfl, h_state⟩, h_step⟩ := h_assumptions
    · simp [h_step]
    · simp [h_state, h_step]

/-- One execution row per state pushed to the state channel. Padding rows are disabled and hold the
initial state. -/
abbrev executionComponent (program : Array (F p)) (h_program : ValidProgram program)
    (initialState : State (F p)) : Component (F p) where
  circuit := executeStep program h_program initialState
  generation := .demand {
    channel := stateChannel program initialState
    surplus := .push
    aggregation := .perOccurrence
    input := [.const 1, .message 0, .message 1, .message 2]
    padding := { input := #[0, initialState.pc, initialState.ap, initialState.fp] }
  }

/-- The state in which a program has run to completion: `pc` points just past the program, where no
further instruction can be fetched. -/
def haltedState (programSize : ℕ) (ap fp : F p) : State (F p) :=
  { pc := programSize, ap, fp }

/-- The public input `(ap, fp)` claims that the program halts with these registers. -/
def verifier (program : Array (F p)) (initialState : State (F p)) :
    Verifier.Program (F p) fieldPair where
  main | (ap, fp) => do
    Verifier.pull (stateChannel program initialState)
      { pc := .const (program.size : F p), ap, fp }
    Verifier.push (stateChannel program initialState) (const initialState)
  Spec
  | (ap, fp), data =>
      (stateChannel program initialState).Guarantees (haltedState program.size ap fp) data
  soundness := by simp_all [circuit_norm, explicit_provable_type, stateChannel, haltedState]

def vm (program : Array (F p)) (h_program : ValidProgram program)
    (initialState : State (F p)) :
    VmTables (F p) fieldPair where
  channel := stateChannel program initialState
  tables := [executionComponent program h_program initialState]
  verifier := verifier program initialState
  tables_channel := by simp [circuit_norm, executeStep, sub_eq_zero]
  verifier_channel := by simp [circuit_norm, verifier]
  verifier_requirements env := by
    simp only [verifier, stateChannel, circuit_norm]
    exact ⟨0, rfl⟩

def soundEnsemble {memorySize : UInt64} (program : Array (F p)) (h_program : ValidProgram program)
    (h_memorySize : memorySize.toNat < p) (initialState : State (F p)) :=
  SoundEnsemble.empty (F p) fieldPair
  |>.addLookup (programLookup program h_program)
  |>.addTable (memoryComponent memorySize h_memorySize)
    (by simp +instances [circuit_norm, memoryComponent, provideMemory])
    (by simp [circuit_norm, memoryComponent, provideMemory, programLookup, memoryChannel])
    (by simp [circuit_norm, memoryComponent, provideMemory, programLookup])
  |>.addFinishedChannel memoryChannel.toRaw
  |>.addVm (vm program h_program initialState)
    (by simp +instances [circuit_norm, vm, programLookup, memoryComponent, provideMemory,
      stateChannel, memoryChannel])
    (by simp +instances [circuit_norm, vm, executeStep, verifier])
    (by simp [circuit_norm, vm, executeStep, verifier, stateChannel,
      programLookup, memoryChannel])
    (by simp [circuit_norm, vm, executeStep, memoryComponent, provideMemory, programLookup])
  |>.withProverInput (fields memorySize.toNat)
    [{ key := memoryValuesKey, width := 1, offset := 0, rows := memorySize.toNat }]

/-- The public statement: some memory of size `memorySize.toNat` makes the program run from
`initialState` to completion with registers `(ap, fp)`. -/
def Spec (program : Array (F p)) (memorySize : UInt64)
    (initialState : State (F p)) : fieldPair (F p) → Prop
  | (ap, fp) => ∃ mem : Array (F p), mem.size = memorySize.toNat ∧ ∃ steps,
      Spec.femtoCairoMachineBoundedExecution program mem (some initialState) steps =
        some (haltedState program.size ap fp)

/-- The prover's assumptions: its memory values make the program run from `initialState` to
completion with registers `(ap, fp)`. -/
def ProverAssumptions (program : Array (F p))
    (memorySize : UInt64) (initialState : State (F p)) :
    fieldPair (F p) → fields memorySize.toNat (F p) → Prop
  | (ap, fp), memoryValues => ∃ steps,
      Spec.femtoCairoMachineBoundedExecution program memoryValues.toArray (some initialState)
        steps = some (haltedState program.size ap fp)

def formalEnsemble {memorySize : UInt64} (program : Array (F p)) (h_program : ValidProgram program)
    (h_memorySize : memorySize.toNat < p) (initialState : State (F p)) :=
  (soundEnsemble program h_program h_memorySize initialState).toFormal (fun _ => True)
    (Spec program memorySize initialState)
    (by simp [circuit_norm, soundEnsemble, vm, memoryComponent])
    (by
      rintro witness - spec
      have hsize := witness.getRows_size_of_fixedColumns
        (component := memoryComponent memorySize h_memorySize)
        (by simp [soundEnsemble, circuit_norm]) rfl
      simp only [memoryComponent, provideMemory, memoryFixedColumns] at hsize
      simp only [circuit_norm, soundEnsemble, vm, verifier, stateChannel] at spec
      obtain ⟨steps, hsteps⟩ := spec
      refine ⟨ memory witness.data, ?_, steps, hsteps ⟩
      rw [memory, Array.size_map]
      exact hsize)
    (ProverAssumptions program memorySize initialState)

/-- End-to-end soundness: a valid proof for the public registers `(ap, fp)` shows that the program,
run on some memory of size `memorySize`, halts with these registers. -/
theorem femtoCairo_soundness {memorySize : UInt64}
    (program : Array (F p)) (h_program : ValidProgram program)
    (h_memorySize : memorySize.toNat < p)
    (initialState : State (F p)) (ap fp : F p) :
    (soundEnsemble program h_program h_memorySize initialState).ensemble.Statement (ap, fp) →
      ∃ mem : Array (F p), mem.size = memorySize.toNat ∧ ∃ steps,
        Spec.femtoCairoMachineBoundedExecution program mem (some initialState) steps =
          some (haltedState program.size ap fp) :=
  (formalEnsemble program h_program h_memorySize initialState).soundness (ap, fp) trivial

namespace Witness

def generate {memorySize : UInt64} (program : Array (F p)) (h_program : ValidProgram program)
    (h_memorySize : memorySize.toNat < p)
    (memoryValues : fields memorySize.toNat (F p)) (initialState : State (F p))
    (finalRegisters : fieldPair (F p)) (fuel : ℕ) :
    Except WitnessGeneration.GenerationError
      (EnsembleWitness (formalEnsemble program h_program h_memorySize initialState).ensemble) :=
  WitnessGeneration.generate (formalEnsemble program h_program h_memorySize initialState).ensemble
    fuel finalRegisters memoryValues

end Witness

end Examples.FemtoCairo.FlatAir
