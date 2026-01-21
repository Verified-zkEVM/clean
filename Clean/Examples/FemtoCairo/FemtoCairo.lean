import Clean.Table.Inductive
import Clean.Gadgets.Bits
import Clean.Utils.Bits
import Clean.Utils.Field
import Clean.Table.Inductive

import Clean.Examples.FemtoCairo.SpecLemmas
import Clean.Examples.FemtoCairo.TypesLemmas

namespace Examples.FemtoCairo
open Gadgets
open Utils.Bits
open Examples.FemtoCairo
open Examples.FemtoCairo.Types
open Examples.FemtoCairo.Spec
variable {p : ℕ} [Fact p.Prime] [p_large_enough: Fact (p > 512)]

/--
  Construct a table that represents a read-only memory containing all pairs (i, f(i)) for i in [0, length).
  - The **program table** it is OK, as it a fixed and public,
    so the verifier always has access to lookups into its table.
  - For the **memory table**, it is committed by the prover, and no constraints are enforced on it.
    For our formalization, we represent it also as a fixed table. This is without loss of generality,
    since we do not make any assumptions on its content, and its role is just to fix a function.

  To represent, e.g., a read-write memory we will need a more complex construction.
-/
def ReadOnlyTableFromFunction
    {n : ℕ} (f : Fin n → (F p)) (h : n < p) [NeZero n] :
    Table (F p) fieldPair
  := .fromStatic {
  name := "ReadOnlyMemory"
  length := n
  row i := (i, f i)
  index := fun (i, _) => i.val
  Spec := fun (i, v) => v = f (Fin.ofNat n i.val) ∧ i.val < n
  contains_iff := by
    rintro ⟨row_index, row_value⟩
    constructor
    · rintro ⟨ i', h' ⟩
      split
      case h_1 i snd h_eq =>
        simp only [Prod.mk.injEq] at h' h_eq
        rw [←h_eq.left, ←h_eq.right, h'.left, h'.right, Fin.ofNat.eq_1]
        have h := Fin.isLt i'
        constructor
        · congr
          rw [←Fin.val_eq_val]
          simp only
          rw [ZMod.val_cast_of_lt (by linarith), Nat.mod_eq_of_lt h]
        · rw [ZMod.val_cast_of_lt (by linarith)]
          assumption
    · intro h
      simp_all only [Fin.ofNat_eq_cast, Prod.mk.injEq]
      use (Fin.ofNat n row_index.val)
      simp only [Fin.ofNat_eq_cast, Fin.val_natCast, and_true]
      rw [Nat.mod_eq_of_lt (by linarith)]
      simp only [ZMod.natCast_val]
      apply_fun ZMod.val
      · rw [ZMod.val_cast_eq_val_of_lt (by linarith)]
      · apply ZMod.val_injective
}

def decodeInstructionMain (instruction : Expression (F p)) : Circuit (F p) (Var DecodedInstruction (F p)) := do
  let bits ← Gadgets.toBits 8 (by linarith [p_large_enough.elim]) instruction
  return {
    instrType := {
      isAdd := (1 : Expression _) - bits[0] - bits[1] + bits[0] * bits[1],
      isMul := bits[0] - bits[0] * bits[1],
      isStoreState := bits[1] - bits[0] * bits[1],
      isLoadState := bits[0] * bits[1]
    },
    mode1 := {
      isDoubleAddressing := (1 : Expression _) - bits[2] - bits[3] + bits[2] * bits[3],
      isApRelative := bits[2] - bits[2] * bits[3],
      isFpRelative := bits[3] - bits[2] * bits[3],
      isImmediate := bits[2] * bits[3]
    },
    mode2 := {
      isDoubleAddressing := (1 : Expression _) - bits[4] - bits[5] + bits[4] * bits[5],
      isApRelative := bits[4] - bits[4] * bits[5],
      isFpRelative := bits[5] - bits[4] * bits[5],
      isImmediate := bits[4] * bits[5]
    },
    mode3 := {
      isDoubleAddressing := (1 : Expression _) - bits[6] - bits[7] + bits[6] * bits[7],
      isApRelative := bits[6] - bits[6] * bits[7],
      isFpRelative := bits[7] - bits[6] * bits[7],
      isImmediate := bits[6] * bits[7]
    }
  }

/--
  Circuit that decodes a femtoCairo instruction into a one-hot representation.
  It returns a `DecodedInstruction` struct containing the decoded fields.
  This circuit is not satisfiable if the input instruction is not correctly encoded.
-/
def decodeInstruction : GeneralFormalCircuit (F p) field DecodedInstruction where
  main := decodeInstructionMain
  localLength _ := 8
  localAdds_eq _ _ _ := by
    simp only [circuit_norm, decodeInstructionMain]
    simp only [Operations.collectAdds, circuit_norm]

  Assumptions
  | instruction, _ => instruction.val < 256

  Spec
  | instruction, output, _ =>
    match Spec.decodeInstruction instruction with
    | some (instr_type, mode1, mode2, mode3) =>
      output.instrType.val = instr_type ∧ output.instrType.isEncodedCorrectly ∧
      output.mode1.val = mode1 ∧ output.mode1.isEncodedCorrectly ∧
      output.mode2.val = mode2 ∧ output.mode2.isEncodedCorrectly ∧
      output.mode3.val = mode3 ∧ output.mode3.isEncodedCorrectly
    | none => False -- impossible, constraints ensure that input < 256

  soundness := by
    circuit_proof_start [Gadgets.toBits, decodeInstructionMain]
    obtain ⟨ h_range_check, h_eq ⟩ := h_holds
    have h_range_check' : ¬ 256 ≤ input.val := by linarith
    simp only [Spec.decodeInstruction, h_range_check', ↓reduceIte]
    simp only [circuit_norm, explicit_provable_type]
    set bits := fieldToBits 8 input with h_bits_def
    rw [Vector.ext_iff] at h_eq
    simp only [Vector.getElem_map, Vector.getElem_mapRange, Expression.eval] at h_eq
    have h_bits_eval0 := h_eq 0 (by norm_num)
    rw [add_zero] at h_bits_eval0
    simp only [h_bits_eval0, h_eq, Nat.reduceLT]
    have h_bits_are_binary := fieldToBits_bits (x := input) (n := 8)
    rw [← h_bits_def] at h_bits_are_binary
    clear h_eq h_range_check h_range_check' h_bits_eval0 h_input h_bits_def
    have h_bits0 := h_bits_are_binary 0 (by norm_num)
    have h_bits1 := h_bits_are_binary 1 (by norm_num)
    have h_bits2 := h_bits_are_binary 2 (by norm_num)
    have h_bits3 := h_bits_are_binary 3 (by norm_num)
    have h_bits4 := h_bits_are_binary 4 (by norm_num)
    have h_bits5 := h_bits_are_binary 5 (by norm_num)
    have h_bits6 := h_bits_are_binary 6 (by norm_num)
    have h_bits7 := h_bits_are_binary 7 (by norm_num)
    and_intros
    · rcases h_bits0 <;> rcases h_bits1 <;> simp_all [DecodedInstructionType.val, ZMod.val_one]
    · rcases h_bits0 <;> rcases h_bits1 <;> simp_all [DecodedInstructionType.isEncodedCorrectly]
    · rcases h_bits2 <;> rcases h_bits3 <;> simp_all [DecodedAddressingMode.val, ZMod.val_one]
    · rcases h_bits2 <;> rcases h_bits3 <;> simp_all [DecodedAddressingMode.isEncodedCorrectly]
    · rcases h_bits4 <;> rcases h_bits5 <;> simp_all [DecodedAddressingMode.val, ZMod.val_one]
    · rcases h_bits4 <;> rcases h_bits5 <;> simp_all [DecodedAddressingMode.isEncodedCorrectly]
    · rcases h_bits6 <;> rcases h_bits7 <;> simp_all [DecodedAddressingMode.val, ZMod.val_one]
    · rcases h_bits6 <;> rcases h_bits7 <;> simp_all [DecodedAddressingMode.isEncodedCorrectly]

  completeness := by circuit_proof_all [Gadgets.toBits, decodeInstructionMain]

/--
  Circuit that fetches a femtoCairo instruction from a read-only program memory,
  given the program counter.
  It returns a `RawInstruction` struct containing the raw instruction and its operands.
  The circuit uses lookups into a read-only table representing the program memory.
  This circuit is not satisfiable if the program counter is out of bounds.
-/
def fetchInstruction
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → (F p)) (h_programSize : programSize < p) :
    GeneralFormalCircuit (F p) field RawInstruction where
  main := fun pc => do
    let programTable := ReadOnlyTableFromFunction program h_programSize

    let rawInstrType ← witness fun eval => program <| Fin.ofNat _ (eval pc).val
    let op1 ← witness fun eval => program <| Fin.ofNat _ (eval (pc + 1)).val
    let op2 ← witness fun eval => program <| Fin.ofNat _ (eval (pc + 2)).val
    let op3 ← witness fun eval => program <| Fin.ofNat _ (eval (pc + 3)).val

    lookup programTable ⟨pc, rawInstrType⟩
    lookup programTable ⟨pc + 1, op1⟩
    lookup programTable ⟨pc + 2, op2⟩
    lookup programTable ⟨pc + 3, op3⟩

    return { rawInstrType, op1, op2, op3 }

  localLength _ := 4
  output _ i₀ := varFromOffset RawInstruction i₀
  localAdds_eq _ _ _ := by simp [circuit_norm]

  Assumptions
  | pc, _ => pc.val + 3 < programSize

  Spec
  | pc, output, _ =>
    match Spec.fetchInstruction program pc with
      | some claimed_output => output = claimed_output
      | none => False -- impossible, lookups ensure that memory accesses are valid
  soundness := by
    circuit_proof_start [ReadOnlyTableFromFunction, Spec.fetchInstruction, Spec.memoryAccess]
    split

    -- the lookups imply that the memory accesses are valid, therefore
    -- here we prove that Spec.memoryAccess never returns none
    case h_2 x h_eq =>
      -- does reading the type return some or none?
      split at h_eq
      · -- does reading op1 return some or none?
        split at h_eq
        · -- does reading op2 return some or none?
          split at h_eq
          · -- does reading op3 return some or none?
            split at h_eq
            · simp_all only [id_eq, Fin.ofNat_eq_cast, and_true, Option.bind_eq_bind,
              Option.bind_some, reduceCtorEq]
            · simp_all only [id_eq, Fin.ofNat_eq_cast, and_false]
          · simp_all only [id_eq, Fin.ofNat_eq_cast, and_false, false_and]
        · simp_all only [id_eq, Fin.ofNat_eq_cast, and_false, false_and]
      · simp_all only [id_eq, Fin.ofNat_eq_cast, and_false, false_and]

    case h_1 rawInstrType claimed_instruction instruction h_eq =>
      simp_all [circuit_norm, explicit_provable_type]
      -- obtain ⟨ h_eq_type, h_eq_op1, h_eq_op2, h_eq_op3 ⟩ := h_eq
      rw [←h_eq]

      simp only [and_assoc] at h_holds
      obtain ⟨ h1, h1', h2, h2', h3, h3', h4, h4' ⟩ := h_holds

      congr <;>
      · rw [←Fin.val_eq_val]
        simp only [Fin.val_natCast, Nat.mod_eq_of_lt h1',
          Nat.mod_eq_of_lt h2', Nat.mod_eq_of_lt h3', Nat.mod_eq_of_lt h4']
  completeness := by
    circuit_proof_start
    simp only [ReadOnlyTableFromFunction, circuit_norm]
    and_intros
    · aesop
    · simp_all; omega
    · aesop
    · simp_all only [id_eq, Fin.ofNat_eq_cast]
      calc
      _ ≤ ZMod.val input + ZMod.val 1 := by apply ZMod.val_add_le
      _ < programSize := by simp only [ZMod.val_one]; omega
    · aesop
    · simp_all only [id_eq, Fin.ofNat_eq_cast]
      calc
      _ ≤ ZMod.val input + ZMod.val 2 := by apply ZMod.val_add_le
      _ < programSize := by
        simp only [ZMod.val_two_eq_two_mod]
        rw [Nat.mod_eq_of_lt] <;> omega
    · aesop
    · simp_all only [id_eq, Fin.ofNat_eq_cast]
      calc
      _ ≤ ZMod.val input + ZMod.val 3 := by apply ZMod.val_add_le
      _ < programSize := by
        rw [← Nat.cast_three, ZMod.val_natCast]
        rw [Nat.mod_eq_of_lt] <;> omega

structure MemoryEntry F where
  address : F
  value : F

instance : ProvableStruct MemoryEntry where
  components := [field, field]
  toComponents := fun { address, value} => .cons address (.cons value .nil)
  fromComponents := fun (.cons address (.cons value .nil)) => { address, value }
  combinedSize := 2

def MemoryTable : Table (F p) MemoryEntry where
  name := "memory"
  Contains table entry := ∃ (ha : entry.address.val < table.size),
    entry.address = table[entry.address.val].address ∧
    entry.value = table[entry.address.val].value

def memorySize (data : ProverData (F p)) : ℕ :=
  let mem := data.getTable MemoryTable
  mem.size

def memoryValue (env : Environment (F p)) (address : Expression (F p)) : F p :=
  let mem := env.data.getTable MemoryTable
  if he : (env address).val < mem.size then
    mem[(env address).val].value
  else 0

def memory (env : ProverData (F p)) : Fin (memorySize env) → F p :=
  let mem := env.getTable MemoryTable
  fun i => mem[i.val].value

-- to satisfy memory lookup constraints, the prover needs to make sure that `memory[addr] = (addr, ·)`
def MemoryCompletenessAssumption (env : ProverData (F p)) : Prop :=
  let mem := env.getTable MemoryTable;
  ∀ (addr : F p) (ha : addr.val < mem.size), mem[addr.val].address = addr

/--
  Circuit that reads a value from a read-only memory, given a state, an offset,
  and an addressing mode.
  It returns the value read from memory, according to the addressing mode.
  - If the addressing is a double addressing, it reads the value at `memory[memory[ap + offset]]`.
  - If the addressing is ap-relative, it reads the value at `memory[ap + offset]`.
  - If the addressing is fp-relative, it reads the value at `memory[fp + offset]`.
  - If the addressing is immediate, it returns the offset itself.
  The circuit uses lookups into a read-only table representing the memory.
  This circuit is not satisfiable if the memory access is out of bounds.
-/
def readFromMemory :
    GeneralFormalCircuit (F p) MemoryReadInput field where
  main := fun { state, offset, mode } => do
    /-
      read into memory for all cases of addressing mode.
      to avoid a completeness issue, we use dummy lookups (0, DUMMY_VALUE),
      where DUMMY_VALUE is the actual memory value at address 0 (which is a valid address since memorySize > 0).

      we do two lookups to cover all cases:
      - in case of double addressing, these are the actual two lookups we need
      - in case of single addressing, the second lookup is (0, DUMMY_VALUE)
      - in case of immediate, both lookups are (0, DUMMY_VALUE)
    -/
    let addr1 <==
      mode.isDoubleAddressing * (state.ap + offset) +
      mode.isApRelative * (state.ap + offset) +
      mode.isFpRelative * (state.fp + offset)

    let value1 ← witness fun env => memoryValue env addr1

    let addr2 <== mode.isDoubleAddressing * value1

    let value2 ← witness fun env => memoryValue env addr2
    lookup MemoryTable ⟨addr1, value1⟩
    lookup MemoryTable ⟨addr2, value2⟩

    -- select the correct value based on the addressing mode
    let value <==
      mode.isDoubleAddressing * value2 +
      mode.isApRelative * value1 +
      mode.isFpRelative * value1 +
      mode.isImmediate * offset

    return value

  localLength _ := 5
  output _ i₀ := var ⟨i₀ + 4⟩
  localAdds_eq _ _ _ := by simp [Operations.collectAdds, circuit_norm]

  Assumptions
  | { state, offset, mode }, env =>
    mode.isEncodedCorrectly ∧
    MemoryCompletenessAssumption env ∧
    -- for completeness, we assume that the memory access succeeds
    ∃ hm : NeZero (memorySize env),
    (Spec.dataMemoryAccess (memory env) offset mode.val state.ap state.fp).isSome

  Spec
  | {state, offset, mode}, output, env =>
    mode.isEncodedCorrectly →
    ∃ hm : NeZero (memorySize env),
    match Spec.dataMemoryAccess (memory env) offset mode.val state.ap state.fp with
      | some value => output = value
      | none => False -- impossible, constraints ensure that memory accesses are valid

  soundness := by
    circuit_proof_start [ReadOnlyTableFromFunction, Spec.dataMemoryAccess,
      Spec.memoryAccess, DecodedAddressingMode.val, DecodedAddressingMode.isEncodedCorrectly,
      memorySize, memoryValue, memory, MemoryEntry]
    intro h_assumptions
    set memoryTable := env.data.getTable MemoryTable with h_memory_table_def
    simp only [MemoryTable] at h_holds

    -- circuit_proof_start did not unpack those, so we manually unpack here
    obtain ⟨isDoubleAddressing, isApRelative, isFpRelative, isImmediate⟩ := input_mode
    obtain ⟨_pc, ap, fp⟩ := input_state

    simp only [id_eq, fromElements, eval, size, toVars, toElements, Vector.map_mk, List.map_toArray,
      List.map_cons, List.map_nil, Vector.getElem_mk, ↓List.getElem_toArray,
      ↓List.getElem_cons_zero, ↓List.getElem_cons_succ, State.mk.injEq,
      DecodedAddressingMode.mk.injEq] at h_holds h_assumptions h_input
    simp only [h_input] at h_holds
    simp only [Option.bind_eq_bind, id_eq]
    obtain ⟨ h_addr1, h_addr2, ⟨ h_addr1_lt, h_mem1 ⟩, ⟨ h_addr2_lt, h_mem2 ⟩, h_value ⟩ := h_holds
    obtain ⟨ h_addr1', h_value1 ⟩ := h_mem1
    obtain ⟨ h_addr2', h_value2 ⟩ := h_mem2

    -- prove that memory is non-empty
    have hm : NeZero (env.data.getTable MemoryTable).size := NeZero.of_gt h_addr1_lt
    use hm

    simp only [h_addr1] at h_value1 h_addr1_lt
    rw [h_value1] at h_addr2
    simp only [h_addr2] at h_value2 h_addr2_lt
    simp only [h_value1, h_value2] at h_value
    clear h_input

    -- does the memory accesses return some or none?
    split

    -- the lookups imply that the memory accesses are valid, therefore
    -- here we prove that Spec.memoryAccess never returns none
    case h_2 x h_spec =>
      -- by cases on the addressing mode, the proof for each case is pretty simple
      rcases h_assumptions with h_mode|h_mode|h_mode|h_mode
      · simp only [h_mode, one_mul, zero_mul, add_zero, ↓reduceIte,
        Option.bind_eq_none_iff, Option.dite_none_right_eq_some, Option.some.injEq,
        dite_eq_right_iff, reduceCtorEq, forall_exists_index,
        forall_apply_eq_imp_iff, and_self] at *
        exact h_spec h_addr1_lt h_addr2_lt
      · simp [h_mode, memoryTable] at h_spec h_addr1_lt
        linarith
      · simp [h_mode, memoryTable] at h_spec h_addr1_lt
        linarith
      · simp [h_mode] at h_spec

    -- handle the case where all memory accesses are valid
    case h_1 rawInstrType _ _ value h_eq =>
      -- by cases on the addressing mode, the proof for each case is pretty simple
      rcases h_assumptions with h_mode|h_mode|h_mode|h_mode
      <;> simp [h_mode, memoryTable] at *
      · simp only [h_addr1_lt, ↓reduceDIte, Option.bind_some, Option.dite_none_right_eq_some,
        Option.some.injEq] at h_eq
        obtain ⟨h, h_eq⟩ := h_eq
        rw [← h_eq, h_value]
      · obtain ⟨h, h_eq⟩ := h_eq
        rw [← h_eq, h_value]
      · obtain ⟨h, h_eq⟩ := h_eq
        rw [← h_eq, h_value]
      · rw [← h_eq, h_value]

  completeness := by
    circuit_proof_start [ReadOnlyTableFromFunction, DecodedAddressingMode.isEncodedCorrectly,
      Spec.dataMemoryAccess, memory, memorySize, memoryValue]
    set addr1 := env.get i₀
    set value1 := env.get (i₀ + 1)
    set addr2 := env.get (i₀ + 2)
    set value2 := env.get (i₀ + 3)
    set value := env.get (i₀ + 4)

    set memoryTable := env.data.getTable MemoryTable with h_memory_table_def
    simp only [MemoryTable]
    obtain ⟨ addr1_def, value1_def, addr2_def, value2_def, value_def ⟩ := h_env
    use addr1_def, addr2_def
    simp only [value_def, and_true]

    -- break up the addressing mode and state
    obtain ⟨isDoubleAddressing, isApRelative, isFpRelative, isImmediate⟩ := input_mode
    obtain ⟨_pc, ap, fp⟩ := input_state
    simp only [circuit_norm, explicit_provable_type, DecodedAddressingMode.mk.injEq, State.mk.injEq] at h_input
    simp only [h_input, DecodedAddressingMode.val, memoryAccess, MemoryCompletenessAssumption] at h_assumptions addr1_def addr2_def ⊢
    obtain ⟨ h_mode_encode, h_mem_completeness, h_pos, h_mem_access ⟩ := h_assumptions

    -- simplify the goal using MemoryCompletenessAssumption and witness info
    suffices h_goal : addr1.val < memoryTable.size ∧ addr2.val < memoryTable.size by
      obtain ⟨ h_addr1_lt, h_addr2_lt ⟩ := h_goal
      constructor
      · use h_addr1_lt
        use h_mem_completeness addr1 h_addr1_lt |>.symm
        rw [value1_def]
        split_ifs <;> trivial
      · use h_addr2_lt
        use h_mem_completeness addr2 h_addr2_lt |>.symm
        rw [value2_def]
        split_ifs <;> trivial

    have : (env.data.getTable MemoryTable).size > 0 := NeZero.pos _
    -- by cases on the addressing mode
    rcases h_mode_encode with h_mode|h_mode|h_mode|h_mode
    <;> simp only [h_mode, one_mul, zero_mul, add_zero, zero_add, reduceIte] at *
    · simp only [Option.bind_eq_bind, Option.isSome_iff_exists, Option.bind_eq_some_iff,
      Option.dite_none_right_eq_some, Option.some.injEq, exists_exists_eq_and, ↓existsAndEq,
      exists_prop, and_true] at h_mem_access
      obtain ⟨ h_addr1_lt, h_addr2_lt ⟩ := h_mem_access
      simp [addr1, addr1_def, addr2, addr2_def, value1_def, memoryTable, h_addr1_lt, h_addr2_lt]
    · simp at h_mem_access
      simp [addr1, addr2, *]
    · simp at h_mem_access
      simp [addr1, addr2, *]
    · simp at h_mem_access
      simp [addr1, addr2, *]

/--
  Circuit that computes the next state of the femtoCairo VM, given the current state,
  a decoded instruction, and the values of the three operands.
  The circuit enforces constraints based on the current instruction type to ensure that
  the state transition is valid, therefore this circuit is not satisfiable
  if the claimed state transition is invalid.
  Returns the next state.
-/
def nextState : GeneralFormalCircuit (F p) StateTransitionInput State where
  main := fun { state, decoded, v1, v2, v3 } => do
    let { instrType := { isAdd, isMul, isStoreState, isLoadState }, .. } := decoded

    -- Witness the claimed next state
    let nextState ← witness fun eval => {
      pc := if eval isLoadState = 1 then eval v1 else eval state.pc + 4
      ap := if eval isLoadState = 1 then eval v2 else eval state.ap
      fp := if eval isLoadState = 1 then eval v3 else eval state.fp
    }

    isAdd * (v3 - (v1 + v2)) === 0

    isMul * (v3 - (v1 * v2)) === 0

    isStoreState * (v1 - state.pc) === 0
    isStoreState * (v2 - state.ap) === 0
    isStoreState * (v3 - state.fp) === 0

    -- TODO make `ifElse` more usable and use it here
    nextState.pc === isLoadState * v1 + (1 - isLoadState) * (state.pc + 4)
    nextState.ap === isLoadState * v2 + (1 - isLoadState) * state.ap
    nextState.fp === isLoadState * v3 + (1 - isLoadState) * state.fp
    return nextState

  localLength _ := 3
  output _ i₀ := varFromOffset State i₀
  localAdds_eq := by sorry

  Assumptions
  | {state, decoded, v1, v2, v3}, _ =>
    DecodedInstructionType.isEncodedCorrectly decoded.instrType ∧
    (Spec.computeNextState (DecodedInstructionType.val decoded.instrType) v1 v2 v3 state).isSome

  Spec
  | {state, decoded, v1, v2, v3}, output, _ =>
    DecodedInstructionType.isEncodedCorrectly decoded.instrType →
    match Spec.computeNextState (DecodedInstructionType.val decoded.instrType) v1 v2 v3 state with
      | some nextState => output = nextState
      | none => False -- impossible, constraints ensure that the transition is valid

  soundness := by
    circuit_proof_start [DecodedInstructionType.isEncodedCorrectly, Spec.computeNextState,
      DecodedInstructionType.val]

    -- unpack the decoded instruction type
    obtain ⟨isAdd, isMul, isStoreState, isLoadState⟩ := input_decoded_instrType
    obtain ⟨pc, ap, fp⟩ := input_state

    simp only [circuit_norm, explicit_provable_type,
      DecodedInstructionType.mk.injEq, State.mk.injEq] at h_holds h_input ⊢
    simp only [h_input] at h_holds

    -- give names to the next state for readability
    set pc_next := env.get i₀
    set ap_next := env.get (i₀ + 1)
    set fp_next := env.get (i₀ + 2)

    -- case analysis on the instruction type
    intro h_assumptions
    rcases h_assumptions with isAdd_cases | isMul_cases | isStoreState_cases | isLoadState_cases
    <;> split <;> simp_all [add_eq_zero_iff_eq_neg]

  completeness := by
    circuit_proof_start [Spec.computeNextState]
    rcases h_assumptions with ⟨ h_encode, h_exec ⟩
    -- Turning DecodedInstructionType into ProvableStruct leads to performance problem in soundness,
    -- that's why manual decomposition follows.
    rcases input_var_decoded_instrType
    rename_i iv_decoded_isAdd iv_decoded_isMul iv_decoded_isStoreState iv_decoded_isLoadState
    rcases input_decoded_instrType
    rename_i i_decoded_isAdd i_decoded_isMul i_decoded_isStoreState i_decoded_isLoadState
    simp only [DecodedInstructionType.isEncodedCorrectly] at h_encode
    simp only [DecodedInstructionType.val] at h_exec
    simp only
    obtain ⟨h_input1, h_input_decoded, h_input_v1, h_input_v2, h_input_v3⟩ := h_input
    obtain ⟨h_input2, h_input_mode1, h_input_mode2, h_input_mode3⟩ := h_input_decoded
    simp only [circuit_norm, explicit_provable_type, DecodedInstructionType.mk.injEq] at h_input2
    rcases input_var_state
    rename_i input_var_state_pc input_var_state_ap input_var_state_fp
    rcases input_state
    rename_i input_state_pc input_state_ap input_state_fp
    simp only [circuit_norm, explicit_provable_type, State.mk.injEq] at h_input1
    simp only [h_input2] at ⊢ h_env
    rcases h_encode with h_add | h_mul | h_load | h_store
    · simp only [h_add, ↓reduceIte, Option.isSome_ite, zero_ne_one] at h_exec h_env ⊢
      ring_nf; simp only [true_and, circuit_norm]; and_intros
      · simp only [← h_exec]; ring_nf
      · have h_env0 := h_env 0
        simp only [explicit_provable_type, Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod,
          add_zero, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero] at h_env0
        simp only [circuit_norm, explicit_provable_type, fromVars, h_env0]; ring_nf
      · have h_env1 := h_env 1
        simp only [explicit_provable_type, Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.one_mod,
          Vector.getElem_mk, List.getElem_toArray, List.getElem_cons, one_ne_zero, ↓reduceDIte] at h_env1
        simp only [circuit_norm, explicit_provable_type, fromVars, h_env1]
      · have h_env2 := h_env 2
        simp only [explicit_provable_type, Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.mod_succ,
          OfNat.ofNat_ne_zero, Nat.add_one_sub_one, one_ne_zero, ↓reduceDIte,
          Vector.getElem_mk, List.getElem_toArray, List.getElem_cons] at h_env2
        simp only [circuit_norm, explicit_provable_type, fromVars, h_env2]
    · simp only [h_mul, zero_ne_one, ↓reduceIte, Option.isSome_ite] at h_exec h_env ⊢
      ring_nf; simp only [true_and, circuit_norm]; and_intros
      · simp only [← h_exec]; ring_nf
      · have h_env0 := h_env 0
        simp only [explicit_provable_type, Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod,
          add_zero, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero] at h_env0
        simp only [circuit_norm, explicit_provable_type, fromVars, h_env0]; ring_nf
      · have h_env1 := h_env 1
        simp only [explicit_provable_type, Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.one_mod,
          Vector.getElem_mk, List.getElem_toArray, List.getElem_cons, one_ne_zero, ↓reduceDIte] at h_env1
        simp only [circuit_norm, explicit_provable_type, fromVars, h_env1]
      · have h_env2 := h_env 2
        simp only [explicit_provable_type, Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.mod_succ,
          OfNat.ofNat_ne_zero, Nat.add_one_sub_one, one_ne_zero, ↓reduceDIte,
          Vector.getElem_mk, List.getElem_toArray, List.getElem_cons] at h_env2
        simp only [circuit_norm, explicit_provable_type, fromVars, h_env2]
    · simp only [h_load, zero_ne_one, ↓reduceIte, Option.isSome_ite] at h_exec h_env ⊢
      ring_nf; simp only [true_and, circuit_norm]; and_intros
      · simp only [h_exec, ← h_input1]; ring_nf
      · simp only [h_exec, ← h_input1]; ring_nf
      · simp only [h_exec, ← h_input1]; ring_nf
      · have h_env0 := h_env 0
        simp only [explicit_provable_type, Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod,
          add_zero, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero] at h_env0
        simp only [circuit_norm, explicit_provable_type, fromVars, h_env0]; ring_nf
      · have h_env1 := h_env 1
        simp only [explicit_provable_type, Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.one_mod,
          Vector.getElem_mk, List.getElem_toArray, List.getElem_cons, one_ne_zero, ↓reduceDIte] at h_env1
        simp only [circuit_norm, explicit_provable_type, fromVars, h_env1]
      · have h_env2 := h_env 2
        simp only [explicit_provable_type, Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.mod_succ,
          OfNat.ofNat_ne_zero, Nat.add_one_sub_one, one_ne_zero, ↓reduceDIte,
          Vector.getElem_mk, List.getElem_toArray, List.getElem_cons] at h_env2
        simp only [circuit_norm, explicit_provable_type, fromVars, h_env2]
    · simp only [h_store, zero_ne_one, ↓reduceIte] at h_exec h_env ⊢
      ring_nf; simp only [true_and, circuit_norm]; and_intros
      · have h_env0 := h_env 0
        simp only [explicit_provable_type, Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod,
          add_zero, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero] at h_env0
        simp only [circuit_norm, explicit_provable_type, fromVars, h_env0]
      · have h_env1 := h_env 1
        simp only [explicit_provable_type, Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.one_mod,
          Vector.getElem_mk, List.getElem_toArray, List.getElem_cons, one_ne_zero, ↓reduceDIte] at h_env1
        simp only [circuit_norm, explicit_provable_type, fromVars, h_env1]
      · have h_env2 := h_env 2
        simp only [explicit_provable_type, Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.mod_succ,
          OfNat.ofNat_ne_zero, Nat.add_one_sub_one, one_ne_zero, ↓reduceDIte,
          Vector.getElem_mk, List.getElem_toArray, List.getElem_cons] at h_env2
        simp only [circuit_norm, explicit_provable_type, fromVars, h_env2]

/--
  The main femtoCairo step circuit, which combines instruction fetch, decode,
  memory accesses, and state transition into a single circuit.
  Given a read-only program memory and a read-only data memory, it takes the current state
  as input and returns the next state as output.
  The circuit is not satisfiable if the state transition is invalid.
-/
def femtoCairoStepElaboratedCircuit
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → (F p)) (h_programSize : programSize < p) :
    ElaboratedCircuit (F p) State State where
    main := fun state => do
      -- Fetch instruction
      let { rawInstrType, op1, op2, op3 } ← fetchInstruction program h_programSize state.pc

      -- Decode instruction
      let decoded ← decodeInstruction rawInstrType

      -- Perform relevant memory accesses
      let v1 ← readFromMemory { state, offset := op1, mode := decoded.mode1 }
      let v2 ← readFromMemory { state, offset := op2, mode := decoded.mode2 }
      let v3 ← readFromMemory { state, offset := op3, mode := decoded.mode3 }

      -- Compute next state
      nextState { state, decoded, v1, v2, v3 }
    localLength := 30
    localAdds_eq _ _ _ := by
      simp only [circuit_norm]
      simp only [Operations.collectAdds, circuit_norm]

def femtoCairoStepSpec
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → (F p))
    (state : State (F p)) (nextState : State (F p)) (data : ProverData (F p)) : Prop :=
  ∃ _hm : NeZero (memorySize data),
  Spec.femtoCairoMachineTransition program (memory data) state = some nextState

/--
  Assumptions required for the FemtoCairo step circuit completeness.
  1. ValidProgramSize: programSize + 3 < p (ensures no field wraparound in address arithmetic)
  2. ValidProgram: All instruction bytes in program memory are < 256
  3. MemoryCompletenessAssumption: memory table is filled correctly
  4. The state transition succeeds (execution doesn't fail)
-/
def femtoCairoStepAssumptions
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → F p)
    (state : State (F p)) (data : ProverData (F p)) : Prop :=
  ValidProgramSize p programSize ∧
  ValidProgram program ∧
  MemoryCompletenessAssumption data ∧
  ∃ _hm : NeZero (memorySize data),
  (Spec.femtoCairoMachineTransition program (memory data) state).isSome

def femtoCairoStepSoundness
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → (F p)) (h_programSize : programSize < p)
    : GeneralFormalCircuit.Soundness (F p) (femtoCairoStepElaboratedCircuit program h_programSize) (femtoCairoStepSpec program) := by
  circuit_proof_start [femtoCairoStepSpec, femtoCairoStepAssumptions, femtoCairoStepElaboratedCircuit,
    Spec.femtoCairoMachineTransition, fetchInstruction, readFromMemory, nextState, decodeInstruction]

  obtain ⟨pc_var, ap_var, fp_var⟩ := input_var
  obtain ⟨pc, ap, fp⟩ := input
  simp only [circuit_norm, explicit_provable_type, State.mk.injEq] at h_input
  obtain ⟨h_input_pc, h_input_ap, h_input_fp⟩ := h_input

  obtain ⟨ c_fetch, c_decode, c_read1, c_read2, c_read3, c_next ⟩ := h_holds

  split at c_fetch
  case h_2 =>
    -- impossible, fetchInstructionCircuit ensures that
    -- instruction fetch is always successful
    contradiction
  case h_1 raw_instruction h_eq =>
    rw [h_input_pc] at h_eq
    rw [h_eq, ←c_fetch]
    simp only [Option.bind_eq_bind, Option.bind_some]

    split at c_decode
    case h_2 =>
      -- impossible, decodeInstruction.circuit ensures that
      -- instruction decode is always successful
      contradiction
    case h_1 instr_type mode1 mode2 mode3 h_eq_decode =>
      simp only [circuit_norm, explicit_provable_type] at h_eq_decode ⊢
      simp only [h_eq_decode, Option.bind_some]
      obtain ⟨ h_instr_type_val, h_instr_type_encoded_correctly, h_mode1_val,
        h_mode1_encoded_correctly, h_mode2_val, h_mode2_encoded_correctly,
        h_mode3_val, h_mode3_encoded_correctly ⟩ := c_decode

      -- satisfy assumptions of read1
      specialize c_read1 h_mode1_encoded_correctly
      rw [h_mode1_val] at c_read1

      -- satisfy assumptions of read2
      specialize c_read2 h_mode2_encoded_correctly
      rw [h_mode2_val] at c_read2

      -- satisfy assumptions of read3
      specialize c_read3 h_mode3_encoded_correctly
      rw [h_mode3_val] at c_read3

      -- satisfy assumptions of next
      specialize c_next h_instr_type_encoded_correctly
      rw [h_instr_type_val] at c_next

      simp only [circuit_norm, explicit_provable_type] at c_read1 c_read2 c_read3 c_next
      rcases c_read1 with ⟨ hm, c_read1 ⟩
      rcases c_read2 with ⟨ hm, c_read2 ⟩
      rcases c_read3 with ⟨ hm, c_read3 ⟩
      use hm

      split at c_read1
      case h_2 =>
        -- impossible, readFromMemory ensures that
        -- memory access is always successful
        contradiction
      case h_1 v1 h_eq_v1 =>
        rw [h_eq_v1, ←c_read1]
        split at c_read2
        case h_2 =>
          -- impossible, readFromMemory ensures that
          -- memory access is always successful
          contradiction
        case h_1 v2 h_eq_v2 =>
          rw [h_eq_v2, ←c_read2]
          split at c_read3
          case h_2 =>
            -- impossible, readFromMemory ensures that
            -- memory access is always successful
            contradiction
          case h_1 v3 h_eq_v3 =>
            rw [h_eq_v3, ←c_read3]
            simp only [Option.bind_some]

            split at c_next
            case h_2 =>
              -- impossible, nextState ensures that
              -- state transition is always successful
              contradiction
            case h_1 next_state h_eq_next =>
              rw [h_eq_next, ←c_next]

def femtoCairoStepCompleteness {programSize : ℕ} [NeZero programSize] (program : Fin programSize → (F p))
  (h_programSize : programSize < p) :
    GeneralFormalCircuit.Completeness (F p) (femtoCairoStepElaboratedCircuit program h_programSize)
      (femtoCairoStepAssumptions program) := by
  circuit_proof_start [femtoCairoStepAssumptions, femtoCairoStepElaboratedCircuit,
    fetchInstruction, decodeInstruction, readFromMemory, nextState]

  obtain ⟨h_valid_size, h_valid_program, h_memory_completeness, h_pos, h_transition_isSome⟩ := h_assumptions

  -- Decompose transition into components
  have h_decompose := Spec.transition_isSome_implies_computeNextState_isSome
    program (memory env.data) input h_transition_isSome
  obtain ⟨raw, decode, v1, v2, v3, h_fetch, h_decode, h_v1, h_v2, h_v3, h_computeNext⟩ := h_decompose

  have h_fetch_isSome : (Spec.fetchInstruction program input.pc).isSome := by
    exact Spec.transition_isSome_implies_fetch_isSome program (memory env.data) input h_transition_isSome
  have h_pc_bound : input.pc.val + 3 < programSize :=
    Spec.fetchInstruction_isSome_implies_pc_bound program h_valid_size input.pc h_fetch_isSome
  have h_instr_bound : raw.rawInstrType.val < 256 := by
    have h_decode_bound := Spec.decodeInstruction_isSome_implies_bound raw.rawInstrType
    simp only [Option.isSome_iff_exists] at h_decode_bound
    exact h_decode_bound ⟨decode, h_decode⟩

  -- Setup: extract subcircuit specs and derive operand equalities
  set fetched := varFromOffset RawInstruction i₀
  rcases raw with ⟨rawInstrType, op1, op2, op3⟩
  simp only at *

  obtain ⟨h_fetch_env, h_decode_env, h_read1_env, h_read2_env, h_read3_env, h_next_env⟩ := h_env
  have h_eval_pc : Expression.eval env input_var.pc = input.pc := by
    rw [← State.eval_pc env input_var, h_input]
  simp only [h_eval_pc] at h_fetch_env
  specialize h_fetch_env h_pc_bound
  simp only [h_fetch, circuit_norm, explicit_provable_type, RawInstruction.mk.injEq] at h_fetch_env
  simp_all

variable {programSize : ℕ} [NeZero programSize] (program : Fin programSize → (F p)) (h_programSize : programSize < p)
variable (h_program : ValidProgramSize p programSize ∧ ValidProgram program)

def femtoCairoStep : GeneralFormalCircuit (F p) State State where
  __ := femtoCairoStepElaboratedCircuit program h_programSize
  Assumptions := femtoCairoStepAssumptions program
  Spec := femtoCairoStepSpec program
  soundness := femtoCairoStepSoundness program h_programSize
  completeness := femtoCairoStepCompleteness program h_programSize
/--
  The femtoCairo table, which defines the step relation for the femtoCairo VM.
  Given a read-only program memory and a read-only data memory, it defines
  the step relation on states of the femtoCairo VM.

  Proving knowledge of a table of length `n` proves the following statement:
  the prover knows a memory function such that the bounded execution of the femtoCairo VM
  for `n` steps from the given initial state, using the given program memory, does not
  return `none`.
-/
def femtoCairoTable (n : ℕ) : InductiveTable (F p) State unit where
  step state _ :=
    femtoCairoStep program h_programSize state

  Spec initialState _ i _ state env : Prop :=
    ∃ hm : NeZero (memorySize env),
    (Spec.femtoCairoMachineBoundedExecution program (memory env) (some initialState) i) = some state

  -- For completeness, we assume that execution on the initial state succeeds, for all steps up to a maximum N
  InputAssumptions i _ _ := i < n
  InitialStateAssumptions initialState env :=
    MemoryCompletenessAssumption env ∧
    ∃ hm : NeZero (memorySize env),
    ∀ i ≤ n, (Spec.femtoCairoMachineBoundedExecution program (memory env) (some initialState) i).isSome

  soundness := by
    intros initial_state i env state_var input_var state input h1 h2 h_inputs h_hold
    simp_all only [circuit_norm, Spec.femtoCairoMachineBoundedExecution, femtoCairoStep, femtoCairoStepSpec]
    aesop

  completeness := by
    intro initialState i env acc_var x_var acc x xs xs_len h_eval h_witnesses
    rintro ⟨ ⟨ h_mem_completeness, hm, h_initial_state ⟩, ⟨ _, h_spec ⟩, h_i⟩
    specialize h_initial_state (i+1) h_i
    simp_all [circuit_norm, Spec.femtoCairoMachineBoundedExecution, femtoCairoStep, femtoCairoStepAssumptions, MemoryCompletenessAssumption]

/--
  The formal table for the femtoCairo VM, which ensures that the execution starts with
  the default initial state (pc=0, ap=0, fp=0).

  The table's statement implies that the state at each row is exactly the state reached by the
  femtoCairo machine after executing that many steps from the initial state.
  In particular, the bounded execution does not return `none`, which means that
  the execution is successful for that many steps.
-/
theorem femtoCairoTableStatement (finalState : State (F p)) :
  let initialState : State (F p) := { pc := 0, ap := 0, fp := 0 };

  ∀ n > 0, ∀ trace data (_ : NeZero (memorySize data)),

  let table := femtoCairoTable program h_programSize h_program n
    |>.toFormal initialState finalState

  table.statement n trace data →
    (Spec.femtoCairoMachineBoundedExecution program (memory data) (some initialState) (n - 1)) = some finalState
  := by
  intro initialState n hn trace data hm table Spec
  simp only [table, FormalTable.statement, InductiveTable.toFormal, femtoCairoTable,
    FemtoCairo.Spec.femtoCairoMachineBoundedExecution] at Spec
  simp_all [exists_true_left]

end Examples.FemtoCairo
