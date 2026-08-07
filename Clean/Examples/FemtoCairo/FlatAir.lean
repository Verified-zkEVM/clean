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
  Guarantees entry data := MemoryTable.Contains (data.getTable MemoryTable) entry

omit [Fact p.Prime] p_large_enough in
lemma memoryEntry_toElements (entry : MemoryEntry (F p)) :
    toElements entry = #v[entry.address, entry.value] := by
  rcases entry with ⟨address, value⟩
  rfl

omit [Fact p.Prime] p_large_enough in
lemma memoryTable_getElem?_eq (data : ProverData (F p)) (i : ℕ) :
    (data.getTable MemoryTable)[i]? =
      Option.map (fromElements (M := MemoryEntry))
        ((data "memory" (size MemoryEntry))[i]?) := by
  rw [show data.getTable MemoryTable =
    (data "memory" (size MemoryEntry)).map fromElements by rfl]
  exact Array.getElem?_map

def readFromMemory : GeneralFormalCircuit (F p) MemoryReadInput field where
  main := fun { state, offset, mode } => do
    let addr1 <==
      mode.isDoubleAddressing * (state.ap + offset) +
      mode.isApRelative * (state.ap + offset) +
      mode.isFpRelative * (state.fp + offset)
    let value1 ← witness (MemoryTable.dataGet addr1.val).value
    let addr2 <== mode.isDoubleAddressing * value1
    let value2 ← witness (MemoryTable.dataGet addr2.val).value
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
    set memoryTable := env.data.getTable MemoryTable with h_memory_table_def
    simp only [MemoryTable] at h_holds
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
    set memoryTable := env.data.getTable MemoryTable with h_memory_table_def
    simp only [MemoryTable]
    obtain ⟨addr1_def, value1_def, addr2_def, value2_def, value_def⟩ := h_env
    use addr1_def, addr2_def
    simp only [value_def, and_true]
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
        rw [value1_def]
        simp [h_addr1_lt]
      · use h_addr2_lt
        use h_mem_completeness addr2 h_addr2_lt |>.symm
        rw [value2_def]
        simp [h_addr2_lt]
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

structure ProviderInput F where
  address : F
  value : F
  multiplicity : F
deriving ProvableStruct

def provideProgram {programSize : ℕ} (program : Fin programSize → F p) :
    GeneralFormalCircuit (F p) ProviderInput unit where
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
  width := 2
  rows := List.finRange programSize |>.map fun i => #[(i.val : F p), program i]
  uniform_width := by simp

def programComponent {programSize : ℕ} (program : Fin programSize → F p)
    (h_programSize : programSize < p) :
    Component (F p) where
  name := "program"
  dataColumns := [0, 1]
  data_columns_lt_input := by change ∀ column ∈ [0, 1], column < 3; simp
  circuit := provideProgram program
  fixedColumns := some (programFixedColumns program)
  fixed_width_le_input := by change 2 ≤ 3; omega
  fixed_assumptions := by
    intro i hi row data hrow _
    simp only [provideProgram]
    change ∃ h : (row[0]?.getD 0).val < programSize,
      row[1]?.getD 0 = program ⟨(row[0]?.getD 0).val, h⟩
    have hrow' : row.extract 0 2 = #[(i : F p), program ⟨i, by
        simpa [programFixedColumns] using hi⟩] := by
      simpa [programFixedColumns] using hrow
    have hi' : i < programSize := by simpa [programFixedColumns] using hi
    have hextractSize : (row.extract 0 2).size = 2 := by
      simpa [programFixedColumns] using congrArg Array.size hrow
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
  width := 1
  rows := List.finRange memorySize |>.map fun address => #[(address.val : F p)]
  uniform_width := by simp

def memoryComponent (memorySize : ℕ) (h_memorySize : memorySize < p) : Component (F p) where
  name := "memory"
  dataColumns := [0, 1]
  data_columns_lt_input := by change ∀ column ∈ [0, 1], column < 3; simp
  circuit := provideMemory
  fixedColumns := some (memoryFixedColumns memorySize)
  fixed_width_le_input := by change 1 ≤ 3; omega
  fixed_assumptions := by
    intro i hi row data hrow hdata
    simp only [provideMemory, MemoryChannel]
    change ∃ ha : (row[0]?.getD 0).val < (data.getTable MemoryTable).size,
      row[0]?.getD 0 = (data.getTable MemoryTable)[(row[0]?.getD 0).val].address ∧
      row[1]?.getD 0 = (data.getTable MemoryTable)[(row[0]?.getD 0).val].value
    rcases hdata with hfalse | hdata
    · contradiction
    let projected : Vector (F p) (size MemoryEntry) :=
      (projectRow [0, 1] row).cast (by rfl)
    change (data "memory" (size MemoryEntry))[i]? =
      some projected at hdata
    have hi : i < memorySize := by simpa [memoryFixedColumns] using hi
    have hrow' : row.extract 0 1 = #[(i : F p)] := by
      simpa [memoryFixedColumns] using hrow
    have hextractSize : (row.extract 0 1).size = 1 := by
      simpa [memoryFixedColumns] using congrArg Array.size hrow
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
    have hdataSize : i < (data "memory" (size MemoryEntry)).size := by
      exact Array.getElem?_eq_some_iff.mp hdata |>.1
    have htypedDataSize : i < (data.getTable MemoryTable).size := by
      change i < ((data "memory" (size MemoryEntry)).map
        (fromElements (M := MemoryEntry))).size
      rw [Array.size_map]
      exact hdataSize
    let entry : MemoryEntry (F p) := { address := row[0]?.getD 0, value := row[1]?.getD 0 }
    have hproject : projected = toElements entry := by
      dsimp only [projected]
      rw [memoryEntry_toElements (p := p)]
      rfl
    have hrawOpt : (data "memory" (size MemoryEntry))[i]? =
        some projected := hdata
    have hentryOpt : (data.getTable MemoryTable)[i]? = some entry := by
      rw [memoryTable_getElem?_eq, hrawOpt, Option.map_some, hproject,
        ProvableType.fromElements_toElements]
    have hentryOptAtAddress :
        (data.getTable MemoryTable)[(row[0]?.getD 0).val]? = some entry := by
      simpa [hindex] using hentryOpt
    have hentry := Array.getElem?_eq_some_iff.mp hentryOptAtAddress |>.2
    refine ⟨hindex ▸ htypedDataSize, ?_, ?_⟩
    · exact congrArg MemoryEntry.address hentry.symm
    · exact congrArg MemoryEntry.value hentry.symm

def StateChannel {programSize : ℕ} (program : Fin programSize → F p)
    (initialState : State (F p)) : Channel (F p) State where
  name := "state"
  Guarantees state data := ∃ steps,
    Spec.femtoCairoMachineBoundedExecution program (memory data) (some initialState) steps =
      some state

def executeStep {programSize : ℕ} (program : Fin programSize → F p)
    (h_programSize : programSize < p) (initialState : State (F p)) :
    GeneralFormalCircuit (F p) State unit where
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
  name := "execution"
  circuit := executeStep program h_programSize initialState

def verifier {programSize : ℕ} (program : Fin programSize → F p)
    (initialState : State (F p)) : GeneralFormalCircuit (F p) State unit where
  main finalState := do
    (StateChannel program initialState).pull finalState
    (StateChannel program initialState).push (const initialState)

  exposedChannels finalState _ := expose (StateChannel program initialState)
    [pulled finalState, pushed (const initialState)]
  exposedChannels_eq := by simp only [circuit_norm]

  ProverAssumptions finalState data _ :=
    (StateChannel program initialState).Guarantees finalState data

  Spec finalState _ data :=
    (StateChannel program initialState).Guarantees finalState data

  channelsWithRequirements := [(StateChannel program initialState).toRaw]

  soundness := by
    circuit_proof_start [StateChannel]
    constructor
    · exact h_holds
    · exact ⟨0, rfl⟩

  completeness := by
    circuit_proof_start [StateChannel]
    exact h_assumptions

def vm {programSize : ℕ} (program : Fin programSize → F p)
    (h_programSize : programSize < p) (initialState : State (F p)) :
    VmTables (F p) State where
  channel := StateChannel program initialState
  tables := [executionComponent program h_programSize initialState]
  verifier := verifier program initialState
  verifier_length_zero := by simp [verifier, circuit_norm]
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
  verifier_channel := by simp [verifier, circuit_norm]
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
  |>.addFinishedChannel MemoryChannel.toRaw
  |>.addVm (vm program h_programSize initialState)
    (by simp +instances [circuit_norm, vm, programComponent, provideProgram,
      memoryComponent, provideMemory, StateChannel, ProgramChannel, MemoryChannel])
    (by simp +instances [circuit_norm, vm, executionComponent, executeStep, verifier])
    (by simp [circuit_norm, vm, executionComponent, executeStep, verifier,
      StateChannel, ProgramChannel, MemoryChannel])

def formalEnsemble {programSize memorySize : ℕ} (program : Fin programSize → F p)
    (h_programSize : programSize < p) (h_memorySize : memorySize < p)
    (initialState : State (F p)) :=
  (soundEnsemble program h_programSize h_memorySize initialState).toFormal _
    (fun _ _ => True)
    (by
      intro publicInput data _ table htable hfixed input data'
      simp [soundEnsemble, circuit_norm] at htable
      rcases htable with hvm | rfl | rfl
      · have heq : table = executionComponent program h_programSize initialState := by
          simpa [vm] using hvm
        subst table
        simp [executionComponent, executeStep]
      · simp [memoryComponent] at hfixed
      · simp [programComponent] at hfixed)

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
  .fixed
    (List.finRange programSize |>.map fun i => #[(i.val : F p), program i, 0])
    (List.finRange programSize |>.map fun i => {
      channel := (ProgramChannel program).name
      direction := .pull
      message := #[(i.val : F p), program i]
      row := i.val
      column := 2
    })

def memoryMode {memorySize : ℕ} (memoryValues : Fin memorySize → F p) : Mode (F p) :=
  .fixed
    (List.finRange memorySize |>.map fun i => #[(i.val : F p), memoryValues i, 0])
    (List.finRange memorySize |>.map fun i => {
      channel := (MemoryChannel (p := p)).name
      direction := .pull
      message := #[(i.val : F p), memoryValues i]
      row := i.val
      column := 2
    })

def config {programSize memorySize : ℕ} (program : Fin programSize → F p)
    (memoryValues : Fin memorySize → F p) (initialState : State (F p))
    (executionRows fuel : ℕ) : Config (F p) where
  modes := [executionMode program initialState, memoryMode memoryValues, programMode program]
  padding := [
    { input := #[0, 0, 0], minimumRows := executionRows },
    { input := #[0, 0, 0], minimumRows := memorySize },
    { input := #[0, 0, 0], minimumRows := programSize }
  ]
  fuel := fuel

def generate {programSize memorySize : ℕ} (program : Fin programSize → F p)
    (h_programSize : programSize < p) (h_memorySize : memorySize < p)
    (memoryValues : Fin memorySize → F p) (initialState finalState : State (F p))
    (executionRows fuel : ℕ) :
    Except String (EnsembleWitness
      (soundEnsemble program h_programSize h_memorySize initialState).ensemble) :=
  Air.Flat.WitnessGeneration.generate
    (soundEnsemble program h_programSize h_memorySize initialState).ensemble
    (config program memoryValues initialState executionRows fuel) finalState

end Witness

end Examples.FemtoCairo.FlatAir
