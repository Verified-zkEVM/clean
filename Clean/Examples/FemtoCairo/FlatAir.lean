import Clean.Air.Vm
import Clean.Air.WitnessGeneration
import Clean.Examples.FemtoCairo.FemtoCairo

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

def memoryValue (env : Environment (F p)) (address : Expression (F p)) : F p :=
  let mem := env.data.getRows "memory" ProviderInput
  if he : (env address).val < mem.size then
    mem[(env address).val].value
  else 0

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

omit [Fact p.Prime] p_large_enough in
lemma memoryRows_getElem?_eq (data : ProverData (F p)) (i : ℕ) :
    (data.getRows "memory" ProviderInput)[i]? =
      Option.map (fromElements (M := ProviderInput))
        ((data "memory" (size ProviderInput))[i]?) := by
  rw [show data.getRows "memory" ProviderInput =
    (data "memory" (size ProviderInput)).map fromElements by rfl]
  exact Array.getElem?_map

def readFromMemory : GeneralFormalCircuit (F p) MemoryReadInput field where
  main := fun { state, offset, mode } => do
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
      memorySize, memoryValue, memory, MemoryEntry, MemoryReadInput.mk.injEq]
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
    split
    case h_2 x h_spec =>
      rcases h_assumptions with h_mode | h_mode | h_mode | h_mode
      · simp only [h_mode, one_mul, zero_mul, add_zero, ↓reduceIte,
          Option.bind_eq_none_iff, Option.dite_none_right_eq_some, Option.some.injEq,
          dite_eq_right_iff, reduceCtorEq, forall_exists_index,
          forall_apply_eq_imp_iff, and_self] at *
        exact h_spec h_addr1_lt h_addr2_lt
      · simp [h_mode, memoryTable] at h_spec h_addr1_lt; linarith
      · simp [h_mode, memoryTable] at h_spec h_addr1_lt; linarith
      · simp [h_mode] at h_spec
    case h_1 rawInstrType _ _ value h_eq =>
      rcases h_assumptions with h_mode | h_mode | h_mode | h_mode
      <;> simp [h_mode, memoryTable] at *
      · simp only [h_addr1_lt, ↓reduceDIte, Option.bind_some,
          Option.dite_none_right_eq_some, Option.some.injEq] at h_eq
        obtain ⟨h, h_eq⟩ := h_eq
        rw [← h_eq, h_value]
      · obtain ⟨h, h_eq⟩ := h_eq; rw [← h_eq, h_value]
      · obtain ⟨h, h_eq⟩ := h_eq; rw [← h_eq, h_value]
      · rw [← h_eq, h_value]

  completeness := by
    circuit_proof_start [MemoryChannel, DecodedAddressingMode.isEncodedCorrectly,
      Spec.dataMemoryAccess, memory, memorySize, memoryValue, MemoryReadInput.mk.injEq]
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
  let { rawInstrType, op1, op2, op3 } ← fetchInstruction program h_programSize state.pc
  let decoded ← Examples.FemtoCairo.decodeInstruction rawInstrType
  let v1 ← readFromMemory { state, offset := op1, mode := decoded.mode1 }
  let v2 ← readFromMemory { state, offset := op2, mode := decoded.mode2 }
  let v3 ← readFromMemory { state, offset := op3, mode := decoded.mode3 }
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
  ValidProgram program ∧
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
  obtain ⟨h_valid_size, h_programSize_u64, h_valid_program, h_memory_completeness,
    h_transition_isSome⟩ := h_assumptions
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
  completeness := by circuit_proof_start

def programFixedColumns {programSize : ℕ} (program : Fin programSize → F p) :
    FixedColumns (F p) where
  height := programSize
  program := .ofFExprs #v[
    .index,
    .listGetAtIndex ((Vector.ofFn program).toList.map .const)
  ]
  valid := by simp [Witgen.RowProgram.Valid, Witgen.RowProgram.ofFExprs,
    Witgen.VExpr.validForRow, Witgen.FExpr.validForRow]

def programComponent {programSize : ℕ} (program : Fin programSize → F p)
    (h_programSize : programSize < p) :
    Component (F p) where
  circuit := provideProgram program
  fixedColumns := some (programFixedColumns program)
  fixed_width_le_input := by change 2 ≤ 3; omega
  Assumptions := fun _ _ => True
  assumptions_imply_circuit := by
    intro i row data hfixed _ _
    rcases hfixed with ⟨hi, hrow⟩
    simp only [provideProgram]
    change ∃ h : (row[0]?.getD 0).val < programSize,
      row[1]?.getD 0 = program ⟨(row[0]?.getD 0).val, h⟩
    have hi' : i < programSize := by simpa [programFixedColumns] using hi
    have hrow' : row.extract 0 2 = #[(i : F p), program ⟨i, hi'⟩] := by
      simpa [programFixedColumns, FixedColumns.width, FixedColumns.row,
        Witgen.RowProgram.ofFExprs, Witgen.RowProgram.eval, Witgen.VExpr.eval,
        Witgen.FExpr.eval, Witgen.evalSteps,
        Witgen.evalList_map_vector_const, hi'] using hrow
    have hextractSize : (row.extract 0 2).size = 2 := by simp [hrow']
    have hrowSize : 2 ≤ row.size := by
      rw [Array.size_extract] at hextractSize
      omega
    have haddress : row[0]?.getD 0 = (i : F p) := by
      calc
        row[0]?.getD 0 = (row.extract 0 2)[0]?.getD 0 := by
          rw [Array.getElem?_eq_getElem (by omega), Array.getElem?_eq_getElem (by omega)]
          simp only [Array.getElem_extract, Nat.zero_add]
        _ = (i : F p) := by rw [hrow']; rfl
    have hvalue : row[1]?.getD 0 = program ⟨i, hi'⟩ := by
      calc
        row[1]?.getD 0 = (row.extract 0 2)[1]?.getD 0 := by
          rw [Array.getElem?_eq_getElem (by omega), Array.getElem?_eq_getElem (by omega)]
          simp only [Array.getElem_extract, Nat.zero_add]
        _ = program ⟨i, hi'⟩ := by rw [hrow']; rfl
    have hval : (row[0]?.getD 0).val = i := by
      rw [haddress, ZMod.val_natCast_of_lt (lt_trans hi' h_programSize)]
    use hval ▸ hi'
    simpa [hval] using hvalue

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
  completeness := by circuit_proof_start

def memoryFixedColumns (memorySize : ℕ) : FixedColumns (F p) where
  height := memorySize
  program := .ofFExprs #v[.index]
  valid := by rfl

def memoryComponent (memorySize : ℕ) (h_memorySize : memorySize < p) : Component (F p) where
  circuit := provideMemory
  fixedColumns := some (memoryFixedColumns memorySize)
  fixed_width_le_input := by change 1 ≤ 3; omega
  Assumptions := fun _ _ => True
  assumptions_imply_circuit := by
    intro i row data hfixed hdata _
    rcases hfixed with ⟨hi, hrow⟩
    simp only [provideMemory, MemoryChannel]
    change ∃ ha : (row[0]?.getD 0).val < (data.getRows "memory" ProviderInput).size,
      row[0]?.getD 0 = (data.getRows "memory" ProviderInput)[(row[0]?.getD 0).val].address ∧
      row[1]?.getD 0 = (data.getRows "memory" ProviderInput)[(row[0]?.getD 0).val].value
    change (data "memory" (size ProviderInput))[i]? =
      some (inputRow ProviderInput row) at hdata
    have hi : i < memorySize := by simpa [memoryFixedColumns] using hi
    have hrow' : row.extract 0 1 = #[(i : F p)] := by
      simpa [memoryFixedColumns, FixedColumns.width, FixedColumns.row,
        Witgen.RowProgram.ofFExprs, Witgen.RowProgram.eval, Witgen.VExpr.eval,
        Witgen.FExpr.eval, Witgen.evalSteps] using hrow
    have hextractSize : (row.extract 0 1).size = 1 := by simp [hrow']
    have hrowSize : 0 < row.size := by
      rw [Array.size_extract] at hextractSize
      omega
    have haddress : row[0]?.getD 0 = (i : F p) := by
      calc
        row[0]?.getD 0 = (row.extract 0 1)[0]?.getD 0 := by
          rw [Array.getElem?_eq_getElem hrowSize, Array.getElem?_eq_getElem (by omega)]
          simp only [Array.getElem_extract, Nat.zero_add]
        _ = (i : F p) := by rw [hrow']; rfl
    have hindex : (row[0]?.getD 0).val = i := by
      rw [haddress, ZMod.val_natCast_of_lt (lt_trans hi h_memorySize)]
    have hdataSize : i < (data "memory" (size ProviderInput)).size := by
      exact Array.getElem?_eq_some_iff.mp hdata |>.1
    have htypedDataSize : i < (data.getRows "memory" ProviderInput).size := by
      change i < ((data "memory" (size ProviderInput)).map
        (fromElements (M := ProviderInput))).size
      rw [Array.size_map]
      exact hdataSize
    let provider : ProviderInput (F p) := {
      address := row[0]?.getD 0
      value := row[1]?.getD 0
      multiplicity := row[2]?.getD 0
    }
    have hinput : inputRow ProviderInput row = toElements provider := by
      rfl
    have hrawOpt : (data "memory" (size ProviderInput))[i]? =
        some (inputRow ProviderInput row) := hdata
    have hproviderOpt : (data.getRows "memory" ProviderInput)[i]? = some provider := by
      rw [memoryRows_getElem?_eq, hrawOpt, Option.map_some, hinput,
        ProvableType.fromElements_toElements]
    have hentryOptAtAddress :
        (data.getRows "memory" ProviderInput)[(row[0]?.getD 0).val]? = some provider := by
      simpa [hindex] using hproviderOpt
    have hprovider := Array.getElem?_eq_some_iff.mp hentryOptAtAddress |>.2
    refine ⟨hindex ▸ htypedDataSize, ?_, ?_⟩
    · exact congrArg ProviderInput.address hprovider.symm
    · exact congrArg ProviderInput.value hprovider.symm

def StateChannel {programSize : ℕ} (program : Fin programSize → F p)
    (initialState : State (F p)) : Channel (F p) State where
  name := "state"
  Guarantees state data := ∃ steps,
    Spec.femtoCairoMachineBoundedExecution program (memory data) (some initialState) steps =
      some state

def executeStep {programSize : ℕ} (program : Fin programSize → F p)
    (h_programSize : programSize < p) (initialState : State (F p)) :
    GeneralFormalCircuit (F p) State unit where
  name := "execution"
  main state := do
    (StateChannel program initialState).pull state
    let nextState ← femtoCairoStep program h_programSize state
    (StateChannel program initialState).push nextState

  exposedChannels state i₀ :=
    let nextState := (femtoCairoStep program h_programSize).output state i₀
    expose (StateChannel program initialState)
      [pulled state, pushed nextState]
  exposedChannels_eq state i₀ := by
    classical
    have hfilter :
        (FlatOperation.interactions
          ((femtoCairoStep program h_programSize).toSubcircuit i₀ state).ops.toFlat).filter
            (fun (interaction : AbstractInteraction (F p)) => decide (interaction.channel =
              (StateChannel program initialState).toRaw)) = [] := by
      rw [List.filter_eq_nil_iff]
      intro interaction hinteraction heq
      have hinteraction' : interaction ∈
          (((femtoCairoStep program h_programSize).main state).operations i₀).interactions := by
        rw [← GeneralFormalCircuit.toSubcircuit_interactions]
        exact hinteraction
      have hchannel : interaction.channel ∈
          (((femtoCairoStep program h_programSize).main state).operations i₀).channels :=
        List.mem_map.mpr ⟨interaction, hinteraction', rfl⟩
      have hsubset := (femtoCairoStep program h_programSize).channels_subset state i₀ hchannel
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
          ((femtoCairoStep program h_programSize).toSubcircuit (i₀ + 0) state).ops.toFlat).filter
            (fun (interaction : AbstractInteraction (F p)) => decide (interaction.channel =
              (StateChannel program initialState).toRaw)) = [] := by
      simpa only [Nat.add_zero] using hfilter
    simp only [circuit_norm, hfilter', List.nil_append]

  ProverAssumptions state data hint :=
    (StateChannel program initialState).Guarantees state data ∧
      (femtoCairoStep program h_programSize).ProverAssumptions state data hint

  Spec _ _ _ := True
  channelsWithRequirements := [(StateChannel program initialState).toRaw]

  soundness := by
    circuit_proof_start [StateChannel, femtoCairoStep, femtoCairoStepSpec,
      Spec.femtoCairoMachineBoundedExecution]
    obtain ⟨steps, hsteps⟩ := h_holds.1
    refine ⟨steps + 1, ?_⟩
    simp only [Spec.femtoCairoMachineBoundedExecution, hsteps]
    exact h_holds.2

  completeness := by
    circuit_proof_start [StateChannel, femtoCairoStep]
    exact h_assumptions

def executionComponent {programSize : ℕ} (program : Fin programSize → F p)
    (h_programSize : programSize < p) (initialState : State (F p)) : Component (F p) where
  circuit := executeStep program h_programSize initialState

def verifier {programSize : ℕ} (program : Fin programSize → F p)
    (initialState : State (F p)) : Verifier.Program (F p) State where
  main finalState := do
    Verifier.pull (StateChannel program initialState) finalState
    Verifier.push (StateChannel program initialState) (const initialState)
  Spec finalState data := (StateChannel program initialState).Guarantees finalState data
  soundness := by
    intro env guarantees
    simp only [circuit_norm, Operations.FullGuarantees,
      AbstractInteraction.Guarantees, Channel.toRaw] at guarantees ⊢
    exact guarantees

def vm {programSize : ℕ} (program : Fin programSize → F p)
    (h_programSize : programSize < p) (initialState : State (F p)) :
    VmTables (F p) State where
  channel := StateChannel program initialState
  tables := [executionComponent program h_programSize initialState]
  unique_names := by simp [executionComponent]
  verifier := verifier program initialState
  tables_channel := by
    rw [List.forall_iff_forall_mem]
    intro table htable
    simp only [List.mem_singleton] at htable
    subst table
    refine ⟨1, (executionComponent program h_programSize initialState).rowInputVar,
      (femtoCairoStep program h_programSize).output
        (executionComponent program h_programSize initialState).rowInputVar
        (executionComponent program h_programSize initialState).rowOffset, ?_, ?_⟩
    · simp [executionComponent, executeStep, circuit_norm]
    · intro env _
      exact Or.inr rfl
  verifier_channel := by
    simp [verifier, circuit_norm, ChannelInteraction.toRaw]
  verifier_requirements env := by
    simp only [verifier, StateChannel, circuit_norm]
    exact ⟨0, rfl⟩

def soundEnsemble {programSize memorySize : ℕ} (program : Fin programSize → F p)
    (h_programSize : programSize < p) (h_memorySize : memorySize < p)
    (initialState : State (F p)) :=
  SoundEnsemble.empty (F p) State
  |>.addTable (programComponent program h_programSize)
    (List.Subset.refl _)
    (by simp [circuit_norm, programComponent, provideProgram])
  |>.addFinishedChannel (ProgramChannel program).toRaw
  |>.addTable (memoryComponent memorySize h_memorySize)
    (by simp +instances [circuit_norm, memoryComponent, provideMemory])
    (by
      have hne : (ProgramChannel program).toRaw ≠ MemoryChannel.toRaw := by
        intro heq
        have hname := congrArg RawChannel.name heq
        change "program" = "memory" at hname
        contradiction
      simp [circuit_norm, memoryComponent, provideMemory, hne])
    (by
      simp only [SoundEnsemble.addFinishedChannel_tables, SoundEnsemble.addTable_tables,
        SoundEnsemble.empty_tables, List.map_cons, List.map_nil, List.mem_singleton]
      simp [memoryComponent, provideMemory, programComponent, provideProgram])
  |>.addFinishedChannel MemoryChannel.toRaw
  |>.addVm (vm program h_programSize initialState)
    (by simp +instances [circuit_norm, vm, programComponent, provideProgram,
      memoryComponent, provideMemory, StateChannel, ProgramChannel, MemoryChannel])
    (by simp +instances [circuit_norm, vm, executionComponent, executeStep, verifier])
    (by simp [circuit_norm, vm, executionComponent, executeStep, verifier,
      StateChannel, ProgramChannel, MemoryChannel])
    (by
      simp only [SoundEnsemble.addFinishedChannel_tables, SoundEnsemble.addTable_tables,
        SoundEnsemble.empty_tables, List.map_append, List.map_cons, List.map_nil]
      simp [vm, executionComponent, executeStep, memoryComponent, provideMemory,
        programComponent, provideProgram])

def formalEnsemble {programSize memorySize : ℕ} (program : Fin programSize → F p)
    (h_programSize : programSize < p) (h_memorySize : memorySize < p)
    (initialState : State (F p)) :=
  (soundEnsemble program h_programSize h_memorySize initialState).toFormal _
    (fun _ _ => True)
    (by
      intro publicInput data _ table htable input
      simp [soundEnsemble, circuit_norm] at htable
      rcases htable with hvm | rfl | rfl
      · have heq : table = executionComponent program h_programSize initialState := by
          simpa [vm] using hvm
        subst table
        simp [executionComponent, executeStep]
      · simp [memoryComponent]
      · simp [programComponent])

namespace Witness

open Air.Flat.WitnessGeneration

def executionMode {programSize : ℕ} (program : Fin programSize → F p)
    (initialState : State (F p)) : Mode (F p) := .demand {
  channel := (StateChannel program initialState).name
  direction := .push
  aggregation := .perOccurrence
  input := { cells := [.message 0, .message 1, .message 2] }
}

def programMode {programSize : ℕ} (program : Fin programSize → F p) : Mode (F p) :=
  .preallocated {
    rows := (programFixedColumns program).height
    input := .ofFExprs #v[.const 0]
    input_valid := by rfl
    handlers := [{ interaction := 0, column := 2 }]
  }

def memoryMode (memorySize : ℕ) : Mode (F p) := .preallocated {
  rows := memorySize
  input := .ofFExprs #v[.proverInputGet .idx, .const 0]
  input_valid := by rfl
  handlers := [{ interaction := 0, column := 2 }]
}

def config {programSize memorySize : ℕ} (program : Fin programSize → F p)
    (initialState : State (F p)) (executionRows fuel : ℕ) : Config (F p) (fields memorySize) where
  modes := [executionMode program initialState, memoryMode memorySize, programMode program]
  padding := [
    { input := #[0, 0, 0], minimumRows := executionRows },
    { input := #[0, 0, 0], minimumRows := memorySize },
    { input := #[0, 0, 0], minimumRows := programSize }
  ]
  fuel := fuel

def generate {programSize memorySize : ℕ} (program : Fin programSize → F p)
    (h_programSize : programSize < p) (h_memorySize : memorySize < p)
    (memoryValues : fields memorySize (F p)) (initialState finalState : State (F p))
    (executionRows fuel : ℕ) :
    Except String (EnsembleWitness
      (soundEnsemble program h_programSize h_memorySize initialState).ensemble) :=
  Air.Flat.WitnessGeneration.generate
    (soundEnsemble program h_programSize h_memorySize initialState).ensemble
    (config program initialState executionRows fuel) finalState memoryValues

end Witness

end Examples.FemtoCairo.FlatAir
