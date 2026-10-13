module

public import Clean.Air.Vm
public import Clean.Air.WitnessGeneration
public import Clean.Examples.FemtoCairo.FemtoCairo

@[expose] public section

namespace Examples.FemtoCairo.FlatAir

open Air.Flat
open Examples.FemtoCairo
open Examples.FemtoCairo.Types
open Examples.FemtoCairo.Spec

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

def memorySize (data : ProverData (F p)) : ℕ :=
  (data.getRows "memory" ProviderInput).size

def memory (data : ProverData (F p)) : Fin (memorySize data) → F p :=
  let mem := data.getRows "memory" ProviderInput
  fun i => mem[i.val].value

def MemoryCompletenessAssumption (data : ProverData (F p)) : Prop :=
  let mem := data.getRows "memory" ProviderInput
  mem.size > 0 ∧ mem.size ≤ 2^64 ∧
    ∀ (address : F p) (ha : address.val < mem.size), mem[address.val].address = address

def ProgramChannel {programSize : ℕ} (program : Fin programSize → F p) :
    Channel (F p) fieldPair where
  name := "program"
  Guarantees
  | (address, value), _ =>
      ∃ h : address.val < programSize, value = program ⟨address.val, h⟩
  ProverGuarantees
  | (address, value), _ =>
      ∃ h : address.val < programSize, value = program ⟨address.val, h⟩

def fetchInstruction
    {programSize : ℕ} (program : Fin programSize → F p) (h_programSize : programSize < p) :
    GeneralFormalCircuit (F p) field RawInstruction where
  main pc := do
    let programVector := Vector.ofFn program
    let rawInstrType ← witness programVector[pc.val]
    let op1 ← witness programVector[pc.val + 1]
    let op2 ← witness programVector[pc.val + 2]
    let op3 ← witness programVector[pc.val + 3]
    (ProgramChannel program).pull (pc, rawInstrType)
    (ProgramChannel program).pull (pc + 1, op1)
    (ProgramChannel program).pull (pc + 2, op2)
    (ProgramChannel program).pull (pc + 3, op3)
    return { rawInstrType, op1, op2, op3 }

  ProverAssumptions
  | pc, _, _ => pc.val + 3 < programSize ∧ programSize ≤ 2^64

  Spec
  | pc, output, _ =>
      match Spec.fetchInstruction program pc with
      | some claimedOutput => output = claimedOutput
      | none => False

  soundness := by
    circuit_proof_start [ProgramChannel, Spec.fetchInstruction, Spec.memoryAccess]
    split
    case h_2 x h_eq => grind
    case h_1 rawInstrType claimedInstruction instruction h_eq =>
      simp_all only [circuit_norm, explicit_provable_type]
      grind

  completeness := by
    circuit_proof_start [ProgramChannel]
    obtain ⟨h_pc_bound, h_programSize_u64⟩ := h_assumptions
    have val_3 : ZMod.val (3 : F p) = 3 := ZMod.val_natCast_of_lt (by linarith)
    have val_2 : ZMod.val (2 : F p) = 2 := ZMod.val_natCast_of_lt (by linarith)
    have val_1 : ZMod.val (1 : F p) = 1 := ZMod.val_one p
    have : input.val < programSize := by linarith
    have : input.val + 1 < programSize := by linarith
    have : input.val + 2 < programSize := by linarith
    have h_no_wrap : input.val + 3 < 2^64 := by omega
    change F p at input
    have : (input + 1).val = input.val + 1 := by field_to_nat
    have : (input + 2).val = input.val + 2 := by field_to_nat
    have : (input + 3).val = input.val + 3 := by field_to_nat
    simp_all

def MemoryChannel : Channel (F p) MemoryEntry where
  name := "memory"
  Guarantees entry data :=
    let table := data.getRows "memory" ProviderInput
    ∃ ha : entry.address.val < table.size,
      entry.address = table[entry.address.val].address ∧
      entry.value = table[entry.address.val].value
  ProverGuarantees entry data :=
    let table := data.getRows "memory" ProviderInput
    ∃ ha : entry.address.val < table.size,
      entry.address = table[entry.address.val].address ∧
      entry.value = table[entry.address.val].value

/-- Name of the hint table holding the prover's memory values, one per address. -/
def memoryValuesKey : String := "memoryValues"

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
    MemoryChannel.pull { address := addr1, value := value1 }
    MemoryChannel.pull { address := addr2, value := value2 }
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
    circuit_proof_start [MemoryChannel, Spec.dataMemoryAccess, Spec.memoryAccess,
      DecodedAddressingMode.val, DecodedAddressingMode.isEncodedCorrectly,
      memorySize, memory, MemoryEntry, MemoryReadInput.mk.injEq]
    set memoryTable := env.data.getRows "memory" ProviderInput with h_memory_table_def
    obtain ⟨isDoubleAddressing, isApRelative, isFpRelative, isImmediate⟩ := input_mode
    obtain ⟨_pc, ap, fp⟩ := input_state
    simp only [CircuitType.eval_expression, fromElements, ProvableType.eval,
      size, toElements, Vector.map_mk, List.map_toArray,
      List.map_cons, List.map_nil, Vector.getElem_mk, ↓List.getElem_toArray,
      ↓List.getElem_cons_zero, ↓List.getElem_cons_succ, State.mk.injEq,
      DecodedAddressingMode.mk.injEq] at h_holds h_assumptions h_input
    simp only [h_input] at h_holds
    simp only [Option.bind_eq_bind]
    obtain ⟨h_addr1, h_addr2, ⟨h_addr1_lt, h_mem1⟩, ⟨h_addr2_lt, h_mem2⟩, h_value⟩ := h_holds
    obtain ⟨h_addr1', h_value1⟩ := h_mem1
    obtain ⟨h_addr2', h_value2⟩ := h_mem2
    simp only [h_addr1] at h_value1 h_addr1_lt
    rw [h_value1] at h_addr2
    simp only [h_addr2] at h_value2 h_addr2_lt
    simp only [h_value1, h_value2] at h_value
    clear h_input
    rcases h_assumptions with h_mode | h_mode | h_mode | h_mode
    · simp only [h_mode, one_mul, zero_mul, add_zero] at h_addr1_lt h_addr2_lt h_value
      simp only [h_mode, ↓reduceIte]
      simp only [← h_memory_table_def, h_addr1_lt, ↓reduceDIte,
        Option.bind_some, h_addr2_lt]
      exact h_value
    · simp only [h_mode, one_mul, zero_mul, add_zero, zero_add] at h_addr1_lt h_value
      simp only [h_mode, zero_ne_one, ↓reduceIte]
      simp only [← h_memory_table_def, h_addr1_lt, ↓reduceDIte]
      exact h_value
    · simp only [h_mode, one_mul, zero_mul, add_zero, zero_add] at h_addr1_lt h_value
      simp only [h_mode, zero_ne_one, ↓reduceIte]
      simp only [← h_memory_table_def, h_addr1_lt, ↓reduceDIte]
      exact h_value
    · simp only [h_mode, one_mul, zero_mul, add_zero, zero_add,
        zero_ne_one, ↓reduceIte] at h_value ⊢
      exact h_value

  completeness := by
    circuit_proof_start [MemoryChannel, DecodedAddressingMode.isEncodedCorrectly,
      Spec.dataMemoryAccess, memory, memorySize, MemoryReadInput.mk.injEq]
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
    · simp only [Option.bind_eq_bind, Option.isSome_iff_exists, Option.bind_eq_some_iff,
        Option.dite_none_right_eq_some, Option.some.injEq, exists_exists_eq_and,
        ↓existsAndEq, exists_prop, and_true] at h_mem_access
      obtain ⟨h_addr1_lt, h_addr2_lt⟩ := h_mem_access
      simp only [addr1, addr1_def, addr2, addr2_def, value1_def, memoryTable]
      refine ⟨h_addr1_lt, ?_⟩
      simp [h_addr1_lt] at h_addr2_lt ⊢
      exact h_addr2_lt
    · simp at h_mem_access; simp [addr1, addr2, *]
    · simp at h_mem_access; simp [addr1, addr2, *]
    · simp at h_mem_access; simp [addr1, addr2, *]

def femtoCairoStepMain {programSize : ℕ} (program : Fin programSize → F p)
    (h_programSize : programSize < p) (state : Var State (F p)) :
    Circuit (F p) (Var State (F p)) := do
  let raw ← fetchInstruction program h_programSize state.pc
  let decoded ← Examples.FemtoCairo.decodeInstruction raw.rawInstrType
  let v1 ← readFromMemory { state, offset := raw.op1, mode := decoded.mode1 }
  let v2 ← readFromMemory { state, offset := raw.op2, mode := decoded.mode2 }
  let v3 ← readFromMemory { state, offset := raw.op3, mode := decoded.mode3 }
  Examples.FemtoCairo.nextState { state, decoded, v1, v2, v3 }

@[reducible]
instance {programSize : ℕ} (program : Fin programSize → F p) (h_programSize : programSize < p) :
    ElaboratedCircuit (F p) State State (femtoCairoStepMain program h_programSize) := by
  elaborate_circuit

def femtoCairoStepSpec {programSize : ℕ} (program : Fin programSize → F p)
    (state nextState : State (F p)) (data : ProverData (F p)) : Prop :=
  Spec.femtoCairoMachineTransition program (memory data) state = some nextState

def femtoCairoStepAssumptions {programSize : ℕ} (program : Fin programSize → F p)
    (state : State (F p)) (data : ProverData (F p)) (_hint : ProverHint (F p)) : Prop :=
  ValidProgramSize p programSize ∧
  programSize ≤ 2^64 ∧
  MemoryCompletenessAssumption data ∧
  (Spec.femtoCairoMachineTransition program (memory data) state).isSome

theorem femtoCairoStepSoundness {programSize : ℕ} (program : Fin programSize → F p)
    (h_programSize : programSize < p) :
    GeneralFormalCircuit.Soundness (F p) (femtoCairoStepMain program h_programSize)
      (fun _ _ => True) (femtoCairoStepSpec program) := by
  circuit_proof_start [femtoCairoStepSpec, femtoCairoStepAssumptions, femtoCairoStepMain,
    Spec.femtoCairoMachineTransition, fetchInstruction, readFromMemory,
    Examples.FemtoCairo.nextState, Examples.FemtoCairo.decodeInstruction,
    Examples.FemtoCairo.decodeInstructionSpec, Gadgets.toBits]
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

theorem femtoCairoStepCompleteness {programSize : ℕ} (program : Fin programSize → F p)
    (h_programSize : programSize < p) :
    GeneralFormalCircuit.Completeness (F p) (femtoCairoStepMain program h_programSize)
      (femtoCairoStepAssumptions program) (fun _ _ _ => True) := by
  circuit_proof_start [femtoCairoStepAssumptions, femtoCairoStepMain,
    fetchInstruction, Examples.FemtoCairo.decodeInstruction, readFromMemory,
    Examples.FemtoCairo.nextState, Gadgets.toBits]
  obtain ⟨h_valid_size, h_programSize_u64, h_memory_completeness, h_transition_isSome⟩ :=
    h_assumptions
  have h_decompose := Spec.transition_isSome_implies_computeNextState_isSome
    program (memory env.data) input h_transition_isSome
  obtain ⟨raw, decode, v1, v2, v3, h_fetch, h_decode, h_v1, h_v2, h_v3,
    h_computeNext⟩ := h_decompose
  have h_fetch_isSome : (Spec.fetchInstruction program input.pc).isSome :=
    Spec.transition_isSome_implies_fetch_isSome program (memory env.data) input h_transition_isSome
  have h_pc_bound : input.pc.val + 3 < programSize :=
    Spec.fetchInstruction_isSome_implies_pc_bound program h_valid_size input.pc h_fetch_isSome
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
  specialize h_fetch_env ⟨h_pc_bound, h_programSize_u64⟩
  simp only [h_fetch, circuit_norm, explicit_provable_type, RawInstruction.mk.injEq] at h_fetch_env
  obtain ⟨h_rawInstrType, h_op1, h_op2, h_op3⟩ := h_fetch_env
  specialize h_decode_env (by rw [h_rawInstrType]; exact h_instr_bound)
  simp only [Examples.FemtoCairo.decodeInstructionSpec, h_rawInstrType, h_decode] at h_decode_env
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
  · rw [h_eval_pc]; exact ⟨h_pc_bound, h_programSize_u64⟩
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

def femtoCairoStep {programSize : ℕ} (program : Fin programSize → F p)
    (h_programSize : programSize < p) : GeneralFormalCircuit (F p) State State where
  main := femtoCairoStepMain program h_programSize
  ProverAssumptions := femtoCairoStepAssumptions program
  Spec := femtoCairoStepSpec program
  soundness := femtoCairoStepSoundness program h_programSize
  completeness := femtoCairoStepCompleteness program h_programSize

def provideProgram {programSize : ℕ} (program : Fin programSize → F p) :
    GeneralFormalCircuit (F p) ProviderInput unit where
  name := "program"
  main | { address, value, multiplicity } => do
    (ProgramChannel program).emit multiplicity (address, value)
  Assumptions
  | { address, value, .. }, data => (ProgramChannel program).Guarantees (address, value) data
  ProverAssumptions
  | { address, value, .. }, data, _ => (ProgramChannel program).Guarantees (address, value) data
  Spec _ _ _ := True
  channelsWithRequirements := [(ProgramChannel program).toRaw]
  soundness := by
    circuit_proof_start [ProgramChannel]
    intro _ _
    exact h_assumptions
  completeness := by
    circuit_proof_start [ProgramChannel]
    exact fun _ => h_assumptions

def programFixedColumns {programSize : UInt64} (program : Fin programSize.toNat → F p) :
    FixedColumns (F p) where
  height := programSize
  program := .ofFExprs #v[
    .ofU64 .idx,
    .listGet ((Vector.ofFn program).toList.map .const) .idx
  ]
  valid := by simp [Witgen.RowProgram.Valid, Witgen.RowProgram.ofFExprs,
    Witgen.VExpr.validForRow, Witgen.FExpr.validForRow, Witgen.U64Expr.validForRow]

def programComponent {programSize : UInt64} (program : Fin programSize.toNat → F p)
    (h_programSize : programSize.toNat < p) :
    Component (F p) where
  circuit := provideProgram program
  fixedColumns := some (programFixedColumns program)
  fixed_width_le_input := by change 2 ≤ 3; omega
  Assumptions := fun _ _ => True
  assumptions_imply_circuit := by
    rintro i ⟨address, value, multiplicity⟩ data ⟨hi, rest, hrow⟩ - -
    simp [programFixedColumns, circuit_norm, explicit_provable_type, Array.getElem?_append] at hi hrow
    have hval : (i.toNat : F p).val = i.toNat := ZMod.val_cast_of_lt (by omega)
    simp [provideProgram, ProgramChannel, hrow, hval, hi]

def provideMemory : GeneralFormalCircuit (F p) ProviderInput unit where
  name := "memory"
  main | { address, value, multiplicity } => do
    MemoryChannel.emit multiplicity { address, value }
  Assumptions
  | { address, value, .. }, data => MemoryChannel.Guarantees { address, value } data
  ProverAssumptions
  | { address, value, .. }, data, _ => MemoryChannel.Guarantees { address, value } data
  Spec _ _ _ := True
  channelsWithRequirements := [MemoryChannel.toRaw]
  soundness := by
    circuit_proof_start [MemoryChannel]
    intro _ _
    exact h_assumptions
  completeness := by
    circuit_proof_start [MemoryChannel]
    exact fun _ => h_assumptions

def memoryFixedColumns (memorySize : UInt64) : FixedColumns (F p) where
  height := memorySize
  program := .ofFExprs #v[.ofU64 .idx]
  valid := by rfl

def memoryComponent (memorySize : UInt64) (h_memorySize : memorySize.toNat < p) :
    Component (F p) where
  circuit := provideMemory
  fixedColumns := some (memoryFixedColumns memorySize)
  fixed_width_le_input := by change 1 ≤ 3; omega
  Assumptions := fun _ _ => True
  assumptions_imply_circuit := by
    rintro i ⟨address, value, multiplicity⟩ data ⟨hi, rest, hrow⟩ hdata -
    simp [memoryFixedColumns, provideMemory, circuit_norm, explicit_provable_type] at hi hrow hdata
    have hval : (i.toNat : F p).val = i.toNat := ZMod.val_cast_of_lt (by omega)
    obtain ⟨hsize, hentry⟩ := Array.getElem?_eq_some_iff.mp hdata
    simp [provideMemory, MemoryChannel, hrow, hval, hsize, hentry]

def StateChannel {programSize : ℕ} (program : Fin programSize → F p)
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
def executeStep {programSize : ℕ} (program : Fin programSize → F p)
    (h_programSize : programSize < p) (initialState : State (F p)) :
    GeneralFormalCircuit (F p) ExecutionInput unit where
  name := "execution"
  main input := do
    -- has to be inline, channels with requirements proof doesn't handle subcircuits
    assertZero (input.enabled * (input.enabled - 1))
    (StateChannel program initialState).pullIf input.enabled input.state
    let nextState ← femtoCairoStep program h_programSize input.state
    (StateChannel program initialState).pushIf input.enabled nextState

  exposedChannels input i₀ :=
    let nextState := (femtoCairoStep program h_programSize).output input.state i₀
    expose (StateChannel program initialState)
      [pulledIf input.enabled input.state, pushedIf input.enabled nextState]
  exposedChannels_eq input i₀ := by
    classical
    have hfilter :
        (FlatOperation.interactions
          ((femtoCairoStep program h_programSize).toSubcircuit i₀ input.state).ops.toFlat).filter
            (fun (interaction : AbstractInteraction (F p)) => decide (interaction.channel =
              (StateChannel program initialState).toRaw)) = [] := by
      rw [List.filter_eq_nil_iff]
      intro interaction hinteraction heq
      have hinteraction' : interaction ∈
          (((femtoCairoStep program h_programSize).main input.state).operations i₀).interactions := by
        rw [← GeneralFormalCircuit.toSubcircuit_interactions]
        exact hinteraction
      have hchannel : interaction.channel ∈
          (((femtoCairoStep program h_programSize).main input.state).operations i₀).channels :=
        List.mem_map.mpr ⟨interaction, hinteraction', rfl⟩
      have hsubset := (femtoCairoStep program h_programSize).channels_subset input.state i₀ hchannel
      have hneProgram : (StateChannel program initialState).toRaw ≠
          (ProgramChannel program).toRaw := by
        intro heq
        have hname := congrArg RawChannel.name heq
        change "state" = "program" at hname
        contradiction
      have hneMemory : (StateChannel program initialState).toRaw ≠ MemoryChannel.toRaw := by
        intro heq
        have hname := congrArg RawChannel.name heq
        change "state" = "memory" at hname
        contradiction
      have hnot : (StateChannel program initialState).toRaw ∉
          (femtoCairoStep program h_programSize).channels := by
        change (StateChannel program initialState).toRaw ∉
          [(ProgramChannel program).toRaw, (ProgramChannel program).toRaw,
            (ProgramChannel program).toRaw, (ProgramChannel program).toRaw,
            MemoryChannel.toRaw, MemoryChannel.toRaw, MemoryChannel.toRaw,
            MemoryChannel.toRaw, MemoryChannel.toRaw, MemoryChannel.toRaw]
        simp [hneProgram, hneMemory]
      have heq' : interaction.channel = (StateChannel program initialState).toRaw :=
        of_decide_eq_true heq
      exact hnot (heq' ▸ hsubset)
    have hfilter' :
        (FlatOperation.interactions
          ((femtoCairoStep program h_programSize).toSubcircuit (i₀ + 0) input.state).ops.toFlat).filter
            (fun (interaction : AbstractInteraction (F p)) => decide (interaction.channel =
              (StateChannel program initialState).toRaw)) = [] := by
      simpa only [Nat.add_zero] using hfilter
    simp only [circuit_norm, hfilter', List.nil_append]

  ProverAssumptions input data hint :=
    (input.enabled = 0 ∨
      input.enabled = 1 ∧ (StateChannel program initialState).Guarantees input.state data) ∧
    (femtoCairoStep program h_programSize).ProverAssumptions input.state data hint

  Spec _ _ _ := True
  channelsWithRequirements := [(StateChannel program initialState).toRaw]

  soundness := by
    circuit_proof_start [StateChannel, femtoCairoStep, femtoCairoStepSpec,
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
    circuit_proof_start [StateChannel, femtoCairoStep]
    obtain ⟨rfl | ⟨rfl, h_state⟩, h_step⟩ := h_assumptions
    · simp [h_step]
    · simp [h_state, h_step]

def executionComponent {programSize : ℕ} (program : Fin programSize → F p)
    (h_programSize : programSize < p) (initialState : State (F p)) : Component (F p) where
  circuit := executeStep program h_programSize initialState

/-- The state in which a program has run to completion: `pc` points just past the program, where
no further instruction can be fetched. -/
def haltedState (programSize : ℕ) (ap fp : F p) : State (F p) :=
  { pc := programSize, ap, fp }

omit p_large_enough in
/-- No transition leaves a halted state. -/
lemma femtoCairoMachineTransition_haltedState {programSize : ℕ}
    (program : Fin programSize → F p) (h_programSize : programSize < p)
    {memorySize : ℕ} (memory : Fin memorySize → F p) (ap fp : F p) :
    Spec.femtoCairoMachineTransition program memory (haltedState programSize ap fp) = none := by
  have hval : (programSize : F p).val = programSize := ZMod.val_cast_of_lt h_programSize
  simp [Spec.femtoCairoMachineTransition, Spec.fetchInstruction, Spec.memoryAccess,
    haltedState, hval]

/-- The public input `(ap, fp)` claims that the program halts with these registers. -/
def verifier {programSize : ℕ} (program : Fin programSize → F p)
    (initialState : State (F p)) : Verifier.Program (F p) fieldPair where
  main | (ap, fp) => do
    Verifier.pull (StateChannel program initialState)
      { pc := .const (programSize : F p), ap, fp }
    Verifier.push (StateChannel program initialState) (const initialState)
  Spec
  | (ap, fp), data =>
      (StateChannel program initialState).Guarantees (haltedState programSize ap fp) data
  soundness := by
    intro env guarantees
    simp only [circuit_norm, explicit_provable_type, Operations.FullGuarantees,
      AbstractInteraction.Guarantees, Channel.toRaw, haltedState] at guarantees ⊢
    exact guarantees

def vm {programSize : ℕ} (program : Fin programSize → F p)
    (h_programSize : programSize < p) (initialState : State (F p)) :
    VmTables (F p) fieldPair where
  channel := StateChannel program initialState
  tables := [executionComponent program h_programSize initialState]
  unique_names := by simp [executionComponent]
  verifier := verifier program initialState
  tables_channel := by
    simp [circuit_norm, executionComponent, executeStep, Component.rowInputVar,
      Component.rowOperations]
    intro env h
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h)
  verifier_channel := by
    simp [verifier, circuit_norm, ChannelInteraction.toRaw]
  verifier_requirements env := by
    simp only [verifier, StateChannel, circuit_norm]
    exact ⟨0, rfl⟩

def soundEnsemble {programSize memorySize : UInt64} (program : Fin programSize.toNat → F p)
    (h_programSize : programSize.toNat < p) (h_memorySize : memorySize.toNat < p)
    (initialState : State (F p)) :=
  SoundEnsemble.empty (F p) fieldPair
  |>.addTable (programComponent program h_programSize)
    (List.Subset.refl _)
    (by simp [circuit_norm, programComponent, provideProgram])
  |>.addFinishedChannel (ProgramChannel program).toRaw
    (by simp [circuit_norm, programComponent, provideProgram, Verifier.Program.empty])
  |>.addTable (memoryComponent memorySize h_memorySize)
    (by simp +instances [circuit_norm, memoryComponent, provideMemory])
    (by
      have hne : (ProgramChannel program).toRaw ≠ MemoryChannel.toRaw := by
        intro heq
        have hname := congrArg RawChannel.name heq
        change "program" = "memory" at hname
        contradiction
      simp [circuit_norm, memoryComponent, provideMemory, hne])
    (by simp [circuit_norm, memoryComponent, provideMemory, programComponent, provideProgram])
    (by simp +instances [circuit_norm, memoryComponent, provideMemory, ProgramChannel,
      MemoryChannel])
  |>.addFinishedChannel MemoryChannel.toRaw
    (by simp +instances [circuit_norm, memoryComponent, provideMemory, programComponent,
      provideProgram, ProgramChannel, MemoryChannel, Verifier.Program.empty])
  |>.addVm (vm program h_programSize initialState)
    (by simp +instances [circuit_norm, vm, programComponent, provideProgram,
      memoryComponent, provideMemory, StateChannel, ProgramChannel, MemoryChannel])
    (by simp +instances [circuit_norm, vm, executionComponent, executeStep, verifier])
    (by simp [circuit_norm, vm, executionComponent, executeStep, verifier,
      StateChannel, ProgramChannel, MemoryChannel])
    (by simp [circuit_norm, vm, executionComponent, executeStep, memoryComponent, provideMemory,
      programComponent, provideProgram])
    (by simp +instances [circuit_norm, vm, executionComponent, executeStep, verifier,
      memoryComponent, provideMemory, programComponent, provideProgram, StateChannel,
      ProgramChannel, MemoryChannel])

omit p_large_enough in
lemma femtoCairoMachineBoundedExecution_cast {programSize : ℕ} (program : Fin programSize → F p)
    {n m : ℕ} (h : n = m) (memory : Fin n → F p) (state : Option (State (F p))) (steps : ℕ) :
    Spec.femtoCairoMachineBoundedExecution program memory state steps =
      Spec.femtoCairoMachineBoundedExecution program (memory ∘ Fin.cast h.symm) state steps := by
  subst h
  rfl

/-- The public statement: some memory of size `memorySize.toNat` makes the program run from
`initialState` to completion with registers `(ap, fp)`. -/
def Spec {programSize : UInt64} (program : Fin programSize.toNat → F p) (memorySize : UInt64)
    (initialState : State (F p)) : fieldPair (F p) → Prop
  | (ap, fp) => ∃ mem : Fin memorySize.toNat → F p, ∃ steps,
      Spec.femtoCairoMachineBoundedExecution program mem (some initialState) steps =
        some (haltedState programSize.toNat ap fp)

/-- The prover's assumptions: its memory values make the program run from `initialState` to
completion with registers `(ap, fp)`, in at least one step, and the run fits the field and the
trace. -/
def ProverAssumptions {programSize : UInt64} (program : Fin programSize.toNat → F p)
    (memorySize : UInt64) (initialState : State (F p)) :
    fieldPair (F p) → fields memorySize.toNat (F p) → Prop
  | (ap, fp), memoryValues => ∃ steps,
      Spec.femtoCairoMachineBoundedExecution program memoryValues.get (some initialState)
        (steps + 1) = some (haltedState programSize.toNat ap fp) ∧
      64 * (steps + programSize.toNat + memorySize.toNat + 8) < p ∧ steps < 2 ^ 62

omit p_large_enough in
/-- The prover's assumptions are no stronger than the public statement. -/
lemma spec_of_proverAssumptions {programSize memorySize : UInt64}
    (program : Fin programSize.toNat → F p) (initialState : State (F p))
    (registers : fieldPair (F p)) (memoryValues : fields memorySize.toNat (F p))
    (h : ProverAssumptions program memorySize initialState registers memoryValues) :
    Spec program memorySize initialState registers :=
  let ⟨_, hsteps, _⟩ := h
  ⟨_, _, hsteps⟩

def formalEnsemble {programSize memorySize : UInt64} (program : Fin programSize.toNat → F p)
    (h_programSize : programSize.toNat < p) (h_memorySize : memorySize.toNat < p)
    (initialState : State (F p)) :=
  (soundEnsemble program h_programSize h_memorySize initialState).toFormal (fun _ => True)
    (Spec program memorySize initialState)
    (Ensemble.assumptionsConsistency_of_components _ <| by
      intro _ _ component hcomponent input data
      simp [soundEnsemble, circuit_norm] at hcomponent
      rcases hcomponent with hvm | rfl | rfl
      · have heq : component = executionComponent program h_programSize initialState := by
          simpa [vm] using hvm
        subst component
        simp [executionComponent, executeStep]
      · simp [memoryComponent]
      · simp [programComponent])
    (by
      rintro witness - spec
      have hsize := witness.getRows_size_of_fixedColumns
        (component := memoryComponent memorySize h_memorySize)
        (by simp [soundEnsemble, circuit_norm]) rfl
      simp only [memoryComponent, provideMemory, memoryFixedColumns] at hsize
      simp only [circuit_norm, soundEnsemble, vm, verifier, StateChannel] at spec
      obtain ⟨steps, hsteps⟩ := spec
      exact ⟨memory witness.data ∘ Fin.cast hsize.symm, steps,
        femtoCairoMachineBoundedExecution_cast program hsize _ _ _ ▸ hsteps⟩)
  |>.withProverInput (fields memorySize.toNat)
    [{ key := memoryValuesKey, width := 1, offset := 0, rows := memorySize.toNat }]
    (ProverAssumptions program memorySize initialState)

/-- End-to-end soundness: a valid proof for the public registers `(ap, fp)` shows that the
program, run on some memory of size `memorySize`, halts with these registers. -/
theorem femtoCairo_soundness {programSize memorySize : UInt64}
    (program : Fin programSize.toNat → F p)
    (h_programSize : programSize.toNat < p) (h_memorySize : memorySize.toNat < p)
    (initialState : State (F p)) (ap fp : F p) :
    (soundEnsemble program h_programSize h_memorySize initialState).ensemble.Statement (ap, fp) →
      ∃ mem : Fin memorySize.toNat → F p, ∃ steps,
        Spec.femtoCairoMachineBoundedExecution program mem (some initialState) steps =
          some (haltedState programSize.toNat ap fp) :=
  (formalEnsemble program h_programSize h_memorySize initialState).soundness (ap, fp) trivial

namespace Witness

open Air.Flat.WitnessGeneration

def executionMode {programSize : ℕ} (program : Fin programSize → F p)
    (initialState : State (F p)) : DemandMode (F p) where
  channel := (StateChannel program initialState).toRaw
  direction := .push
  aggregation := .perOccurrence
  input := { cells := [.const 1, .message 0, .message 1, .message 2] }

def programMode (programSize : UInt64) : PreallocatedMode (F p) where
  rows := programSize
  input := .ofFExprs #v[.const 0]
  input_valid := by rfl
  handlers := [{ interaction := 0, column := 2 }]

/-- Memory rows hold the prover's memory values, read from the private input. -/
def memoryMode (memorySize : UInt64) : PreallocatedMode (F p) where
  rows := memorySize
  input := .ofFExprs #v[.hintGet memoryValuesKey 1 .idx 0, .const 0]
  input_valid := by rfl
  handlers := [{ interaction := 0, column := 2 }]

/-- The generation plan. Disabled execution rows at the initial state pad the execution table. -/
def plan {programSize memorySize : UInt64} (program : Fin programSize.toNat → F p)
    (h_programSize : programSize.toNat < p) (initialState : State (F p)) :
    GenerationPlan (F p) where
  components := [
    ((executeStep program h_programSize initialState).name, {
      mode := .demand (executionMode program initialState)
      padding := {
        input := #[0, initialState.pc, initialState.ap, initialState.fp]
        minimumRows := 8 } }),
    ((provideMemory (p := p)).name, {
      mode := .preallocated (memoryMode memorySize)
      padding := { input := #[0, 0, 0], minimumRows := memorySize } }),
    ((provideProgram program).name, {
      mode := .preallocated (programMode programSize)
      padding := { input := #[0, 0, 0], minimumRows := programSize } })
  ]

def generate {programSize memorySize : UInt64} (program : Fin programSize.toNat → F p)
    (h_programSize : programSize.toNat < p) (h_memorySize : memorySize.toNat < p)
    (memoryValues : fields memorySize.toNat (F p)) (initialState : State (F p))
    (finalRegisters : fieldPair (F p)) :
    Except GenerationError (EnsembleWitness
      (formalEnsemble program h_programSize h_memorySize initialState).ensemble) :=
  Air.Flat.WitnessGeneration.generate (formalEnsemble program h_programSize h_memorySize initialState)
    (plan (memorySize := memorySize) program h_programSize initialState)
    finalRegisters memoryValues

end Witness

end Examples.FemtoCairo.FlatAir
