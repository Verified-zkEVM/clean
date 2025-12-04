import Clean.Examples.FemtoCairo.Spec

/-!
# Helper lemmas for FemtoCairo completeness proofs

This file contains lemmas about the FemtoCairo specification that are used
in proving completeness of the circuit.
-/

namespace Examples.FemtoCairo.Spec
open Utils.Bits
open Examples.FemtoCairo.Types
variable {p : ℕ} [Fact p.Prime] [p_large_enough: Fact (p > 512)]

omit p_large_enough in
/-- Adding a natural number to a field element preserves the value when no wraparound occurs -/
lemma ZMod_val_add_nat (x : F p) (n : ℕ) (h : x.val + n < p) :
    (x + n).val = x.val + n := by
  calc (x + n).val = (x.val + (n : ZMod p).val) % p := ZMod.val_add x n
    _ = (x.val + n) % p := by rw [ZMod.val_natCast_of_lt (by omega : n < p)]
    _ = x.val + n := Nat.mod_eq_of_lt h

omit [Fact p.Prime] p_large_enough in
/-- If memoryAccess succeeds, the address is in bounds -/
lemma memoryAccess_isSome_implies_bounds {n : ℕ} [NeZero n]
    (memory : Fin n → F p) (addr : F p)
    (h : (memoryAccess memory addr).isSome) : addr.val < n := by
  simp only [memoryAccess, Option.isSome_iff_exists] at h
  split at h
  case isTrue h_bound => exact h_bound
  case isFalse => simp at h

omit [Fact p.Prime] p_large_enough in
/-- If memoryAccess returns some value, the address is in bounds -/
lemma memoryAccess_eq_some_implies_bounds {n : ℕ} [NeZero n]
    (memory : Fin n → F p) (addr : F p) (v : F p)
    (h : memoryAccess memory addr = some v) : addr.val < n :=
  memoryAccess_isSome_implies_bounds memory addr (Option.isSome_iff_exists.mpr ⟨v, h⟩)

omit p_large_enough in
/-- If decodeInstruction succeeds, the instruction value is < 256 -/
lemma decodeInstruction_isSome_implies_bound (instr : F p)
    (h : (decodeInstruction instr).isSome) : instr.val < 256 := by
  simp only [decodeInstruction] at h
  split at h
  case isTrue h_ge => simp at h
  case isFalse h_lt => omega

omit p_large_enough in
/-- If decodeInstruction returns some value, the instruction value is < 256 -/
lemma decodeInstruction_eq_some_implies_bound (instr : F p) (result : ℕ × ℕ × ℕ × ℕ)
    (h : decodeInstruction instr = some result) : instr.val < 256 :=
  decodeInstruction_isSome_implies_bound instr (Option.isSome_iff_exists.mpr ⟨result, h⟩)

omit p_large_enough in
/-- If femtoCairoMachineTransition succeeds, fetchInstruction succeeds -/
lemma transition_isSome_implies_fetch_isSome
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → F p)
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → F p)
    (state : State (F p))
    (h : (femtoCairoMachineTransition program memory state).isSome) :
    (fetchInstruction program state.pc).isSome := by
  simp only [femtoCairoMachineTransition, Option.isSome_iff_exists] at h
  obtain ⟨next, h_next⟩ := h
  simp only [Option.bind_eq_bind] at h_next
  cases h_fetch : fetchInstruction program state.pc
  · simp [h_fetch] at h_next
  · simp

omit p_large_enough in
/-- If fetchInstruction succeeds and programSize + 3 < p (no wraparound), then pc.val + 3 < programSize -/
lemma fetchInstruction_isSome_implies_pc_bound
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → F p)
    (h_valid_size : ValidProgramSize (p := p) programSize)
    (pc : F p)
    (h : (fetchInstruction program pc).isSome) : pc.val + 3 < programSize := by
  -- ValidProgramSize ensures programSize + 3 < p, so no wraparound can occur.
  -- From fetchInstruction succeeding, we know (pc + 3).val < programSize.
  -- Since programSize + 3 < p, we have (pc + 3).val < p - 3.
  -- For any pc.val < programSize, pc.val + 3 < programSize + 3 < p.
  -- Therefore no wraparound: (pc + 3).val = pc.val + 3, and we conclude pc.val + 3 < programSize.
  simp only [fetchInstruction, Option.isSome_iff_exists] at h
  obtain ⟨raw, h_raw⟩ := h
  simp only [Option.bind_eq_bind] at h_raw
  cases h0 : memoryAccess program pc with
  | none => simp [h0] at h_raw
  | some v0 =>
    cases h1 : memoryAccess program (pc + 1) with
    | none => simp [h0, h1] at h_raw
    | some v1 =>
      cases h2 : memoryAccess program (pc + 2) with
      | none => simp [h0, h1, h2] at h_raw
      | some v2 =>
        cases h3 : memoryAccess program (pc + 3) with
        | none => simp [h0, h1, h2, h3] at h_raw
        | some v3 =>
          -- Extract bound from h0: pc.val < programSize
          have bound0 := memoryAccess_eq_some_implies_bounds program pc v0 h0
          have bound3 := memoryAccess_eq_some_implies_bounds program (pc + 3) v3 h3
          -- ValidProgramSize says programSize + 3 < p
          simp only [ValidProgramSize] at h_valid_size
          -- From pc.val < programSize and programSize + 3 < p, we get pc.val + 3 < p
          have h_no_wrap : pc.val + 3 < p := by omega
          -- With no wraparound, (pc + 3).val = pc.val + 3
          have h_eq : (pc + 3).val = pc.val + 3 := ZMod_val_add_nat pc 3 h_no_wrap
          omega

omit p_large_enough in
/-- If transition succeeds, decode succeeds -/
lemma transition_isSome_implies_decode_isSome
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → F p)
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → F p)
    (state : State (F p))
    (h : (femtoCairoMachineTransition program memory state).isSome) :
    ∃ raw, fetchInstruction program state.pc = some raw ∧
           (decodeInstruction raw.rawInstrType).isSome := by
  simp only [femtoCairoMachineTransition, Option.isSome_iff_exists] at h
  obtain ⟨next, h_next⟩ := h
  simp only [Option.bind_eq_bind] at h_next
  cases h_fetch : fetchInstruction program state.pc with
  | none => simp [h_fetch] at h_next
  | some raw =>
    use raw
    constructor
    · rfl
    · simp only [h_fetch, Option.bind_some] at h_next
      cases h_decode : decodeInstruction raw.rawInstrType with
      | none => simp [h_decode] at h_next
      | some _ => simp

omit p_large_enough in
/-- If transition succeeds with ValidProgram, the fetched instruction type is < 256 -/
lemma transition_isSome_with_valid_program_implies_instr_bound
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → F p)
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → F p)
    (state : State (F p))
    (_h_valid : ValidProgram program)
    (h_trans : (femtoCairoMachineTransition program memory state).isSome) :
    ∃ raw, fetchInstruction program state.pc = some raw ∧ raw.rawInstrType.val < 256 := by
  obtain ⟨raw, h_fetch, h_decode⟩ := transition_isSome_implies_decode_isSome program memory state h_trans
  use raw
  constructor
  · exact h_fetch
  · exact decodeInstruction_isSome_implies_bound raw.rawInstrType h_decode

omit p_large_enough in
/-- If transition succeeds, all intermediate steps succeed -/
lemma transition_isSome_implies_computeNextState_isSome
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → F p)
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → F p)
    (state : State (F p))
    (h : (femtoCairoMachineTransition program memory state).isSome) :
    ∃ raw decode v1 v2 v3,
      fetchInstruction program state.pc = some raw ∧
      decodeInstruction raw.rawInstrType = some decode ∧
      dataMemoryAccess memory raw.op1 decode.2.1 state.ap state.fp = some v1 ∧
      dataMemoryAccess memory raw.op2 decode.2.2.1 state.ap state.fp = some v2 ∧
      dataMemoryAccess memory raw.op3 decode.2.2.2 state.ap state.fp = some v3 ∧
      (computeNextState decode.1 v1 v2 v3 state).isSome := by
  -- The transition is a chain of Option.bind operations. If the whole chain returns some,
  -- each intermediate step must have returned some.
  simp only [femtoCairoMachineTransition, Option.isSome_iff_exists] at h
  obtain ⟨nextState, h_next⟩ := h
  simp only [Option.bind_eq_bind] at h_next
  -- Case on fetchInstruction
  cases h_fetch : fetchInstruction program state.pc with
  | none => simp [h_fetch] at h_next
  | some raw =>
    simp only [h_fetch, Option.bind_some] at h_next
    -- Case on decodeInstruction
    cases h_decode : decodeInstruction raw.rawInstrType with
    | none => simp [h_decode] at h_next
    | some decode =>
      simp only [h_decode, Option.bind_some] at h_next
      -- Case on first dataMemoryAccess (uses decode.2.1 = mode1)
      cases h_v1 : dataMemoryAccess memory raw.op1 decode.2.1 state.ap state.fp with
      | none => simp [h_v1] at h_next
      | some v1 =>
        simp only [h_v1, Option.bind_some] at h_next
        -- Case on second dataMemoryAccess (uses decode.2.2.1 = mode2)
        cases h_v2 : dataMemoryAccess memory raw.op2 decode.2.2.1 state.ap state.fp with
        | none => simp [h_v2] at h_next
        | some v2 =>
          simp only [h_v2, Option.bind_some] at h_next
          -- Case on third dataMemoryAccess (uses decode.2.2.2 = mode3)
          cases h_v3 : dataMemoryAccess memory raw.op3 decode.2.2.2 state.ap state.fp with
          | none => simp [h_v3] at h_next
          | some v3 => aesop

omit p_large_enough in
/--
If bounded execution for n steps reaches `state`, and bounded execution for n+1 steps succeeds,
then the transition from `state` succeeds.

The recursion structure is:
  boundedExec init (n+1) = boundedExec init n >>= transition
So if boundedExec init n = some state and boundedExec init (n+1).isSome,
then transition(state).isSome.
-/
lemma transition_isSome_of_boundedExecution_succ_isSome
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → F p)
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → F p)
    (initialState : Option (State (F p))) (state : State (F p)) (n : ℕ)
    (h_n : femtoCairoMachineBoundedExecution program memory initialState n = some state)
    (h_succ : (femtoCairoMachineBoundedExecution program memory initialState (n + 1)).isSome) :
    (femtoCairoMachineTransition program memory state).isSome := by
  -- boundedExec init (n+1) = boundedExec init n >>= transition
  simp only [femtoCairoMachineBoundedExecution, Option.isSome_iff_exists] at h_succ
  obtain ⟨finalState, h_final⟩ := h_succ
  -- h_final : (boundedExec init n >>= transition) = some finalState
  rw [h_n] at h_final
  aesop

omit [Fact (Nat.Prime p)] p_large_enough in
/-- ValidProgram ensures any program access returns a value < 256 -/
lemma validProgram_bound {programSize : ℕ} [NeZero programSize] {program : Fin programSize → F p}
    (h_valid : ValidProgram program) (i : Fin programSize) :
    (program i).val < 256 := h_valid i

omit [Fact (Nat.Prime p)] p_large_enough in
/-- ValidProgram + Fin.ofNat gives bound < 256 (useful when index comes from witness computation) -/
lemma validProgram_bound_at_ofNat {programSize : ℕ} [NeZero programSize] {program : Fin programSize → F p}
    (h_valid : ValidProgram program) (n : ℕ) :
    (program (Fin.ofNat programSize n)).val < 256 := h_valid _

omit p_large_enough in
/-- If decodeInstruction succeeds, the result encodes a valid instruction type -/
lemma decodeInstruction_eq_some_implies_isEncodedCorrectly (instr : F p) (result : ℕ × ℕ × ℕ × ℕ)
    (h : decodeInstruction instr = some result) :
    Types.DecodedInstructionType.isEncodedCorrectly (p := p) {
      isAdd := if result.1 = 0 then 1 else 0
      isMul := if result.1 = 1 then 1 else 0
      isStoreState := if result.1 = 2 then 1 else 0
      isLoadState := if result.1 = 3 then 1 else 0
    } := by
  simp only [decodeInstruction] at h
  split at h
  case isTrue => simp at h
  case isFalse h_lt =>
    simp only [Option.some.injEq] at h
    rcases h with ⟨rfl, _, _, _⟩
    -- result.1 = instr.val % 4, which is 0, 1, 2, or 3
    -- Use fieldToBits_bits: each bit is 0 or 1
    have h_bit0 := fieldToBits_bits (n := 8) (x := instr) 0 (by omega)
    have h_bit1 := fieldToBits_bits (n := 8) (x := instr) 1 (by omega)
    -- Case split on bit values
    rcases h_bit0 with h0_zero | h0_one <;> rcases h_bit1 with h1_zero | h1_one
    · -- bit0 = 0, bit1 = 0 → value = 0
      left
      simp +decide [h0_zero, h1_zero]
    · -- bit0 = 0, bit1 = 1 → value = 2
      right; right; left; simp +decide [h0_zero, h1_one, ZMod.val_one]
    · -- bit0 = 1, bit1 = 0 → value = 1
      right; left; simp +decide [h0_one, h1_zero, ZMod.val_one]
    · -- bit0 = 1, bit1 = 1 → value = 3
      right; right; right; simp +decide [h0_one, h1_one, ZMod.val_one]

omit p_large_enough in
/-- If decodeInstruction succeeds, all addressing modes are encoded correctly -/
lemma decodeInstruction_eq_some_implies_modes_encoded (instr : F p) (result : ℕ × ℕ × ℕ × ℕ)
    (h : decodeInstruction instr = some result) :
    let mode1 := { isDoubleAddressing := if result.2.1 = 0 then (1 : F p) else 0
                   isApRelative := if result.2.1 = 1 then 1 else 0
                   isFpRelative := if result.2.1 = 2 then 1 else 0
                   isImmediate := if result.2.1 = 3 then 1 else 0 }
    let mode2 := { isDoubleAddressing := if result.2.2.1 = 0 then (1 : F p) else 0
                   isApRelative := if result.2.2.1 = 1 then 1 else 0
                   isFpRelative := if result.2.2.1 = 2 then 1 else 0
                   isImmediate := if result.2.2.1 = 3 then 1 else 0 }
    let mode3 := { isDoubleAddressing := if result.2.2.2 = 0 then (1 : F p) else 0
                   isApRelative := if result.2.2.2 = 1 then 1 else 0
                   isFpRelative := if result.2.2.2 = 2 then 1 else 0
                   isImmediate := if result.2.2.2 = 3 then 1 else 0 }
    Types.DecodedAddressingMode.isEncodedCorrectly mode1 ∧
    Types.DecodedAddressingMode.isEncodedCorrectly mode2 ∧
    Types.DecodedAddressingMode.isEncodedCorrectly mode3 := by
  simp only [decodeInstruction] at h
  split at h
  case isTrue => simp at h
  case isFalse h_lt =>
    simp only [Option.some.injEq] at h
    rcases h with ⟨_, rfl, rfl, rfl⟩
    -- Each mode value is derived from different bit pairs of the instruction
    -- mode1 uses bits 2-3, mode2 uses bits 4-5, mode3 uses bits 6-7
    -- Use fieldToBits_bits: each bit is 0 or 1
    have h_bit2 := fieldToBits_bits (n := 8) (x := instr) 2 (by omega)
    have h_bit3 := fieldToBits_bits (n := 8) (x := instr) 3 (by omega)
    have h_bit4 := fieldToBits_bits (n := 8) (x := instr) 4 (by omega)
    have h_bit5 := fieldToBits_bits (n := 8) (x := instr) 5 (by omega)
    have h_bit6 := fieldToBits_bits (n := 8) (x := instr) 6 (by omega)
    have h_bit7 := fieldToBits_bits (n := 8) (x := instr) 7 (by omega)
    -- Helper tactic for the mode proofs
    refine ⟨?mode1, ?mode2, ?mode3⟩
    -- mode1: bits 2-3
    case mode1 =>
      rcases h_bit2 with h2_zero | h2_one <;> rcases h_bit3 with h3_zero | h3_one
      · left; simp +decide [h2_zero, h3_zero]
      · right; right; left; simp +decide [h2_zero, h3_one, ZMod.val_one]
      · right; left; simp +decide [h2_one, h3_zero, ZMod.val_one]
      · right; right; right; simp +decide [h2_one, h3_one, ZMod.val_one]
    -- mode2: bits 4-5
    case mode2 =>
      rcases h_bit4 with h4_zero | h4_one <;> rcases h_bit5 with h5_zero | h5_one
      · left; simp +decide [h4_zero, h5_zero]
      · right; right; left; simp +decide [h4_zero, h5_one, ZMod.val_one]
      · right; left; simp +decide [h4_one, h5_zero, ZMod.val_one]
      · right; right; right; simp +decide [h4_one, h5_one, ZMod.val_one]
    -- mode3: bits 6-7
    case mode3 =>
      rcases h_bit6 with h6_zero | h6_one <;> rcases h_bit7 with h7_zero | h7_one
      · left; simp +decide [h6_zero, h7_zero]
      · right; right; left; simp +decide [h6_zero, h7_one, ZMod.val_one]
      · right; left; simp +decide [h6_one, h7_zero, ZMod.val_one]
      · right; right; right; simp +decide [h6_one, h7_one, ZMod.val_one]

omit [Fact (Nat.Prime p)] p_large_enough in
/-- If dataMemoryAccess succeeds, specific accessed addresses are in bounds -/
lemma dataMemoryAccess_mode0_bound
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → F p)
    (offset ap fp result : F p)
    (h : dataMemoryAccess memory offset 0 ap fp = some result) :
    (ap + offset).val < memorySize ∧
    ∃ addr', memoryAccess memory (ap + offset) = some addr' ∧ addr'.val < memorySize := by
  simp only [dataMemoryAccess, Option.bind_eq_bind] at h
  cases h_first : memoryAccess memory (ap + offset) with
  | none => simp [h_first] at h
  | some addr' =>
    simp only [h_first, Option.bind_some] at h
    simp only [memoryAccess] at h_first
    split at h_first
    case isTrue h_lt =>
      simp only [Option.some.injEq] at h_first
      exact ⟨h_lt, addr', rfl, by simp only [memoryAccess] at h; split at h <;> simp_all⟩
    case isFalse h_neg =>
      simp at h_first

omit [Fact (Nat.Prime p)] p_large_enough in
/-- If dataMemoryAccess succeeds in mode 1 (ap-relative), the address is in bounds -/
lemma dataMemoryAccess_mode1_bound
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → F p)
    (offset ap fp result : F p)
    (h : dataMemoryAccess memory offset 1 ap fp = some result) :
    (ap + offset).val < memorySize := by
  simp only [dataMemoryAccess, memoryAccess] at h
  split at h <;> simp_all

omit [Fact (Nat.Prime p)] p_large_enough in
/-- If dataMemoryAccess succeeds in mode 2 (fp-relative), the address is in bounds -/
lemma dataMemoryAccess_mode2_bound
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → F p)
    (offset ap fp result : F p)
    (h : dataMemoryAccess memory offset 2 ap fp = some result) :
    (fp + offset).val < memorySize := by
  simp only [dataMemoryAccess, memoryAccess] at h
  split at h <;> simp_all

omit p_large_enough in
/-- If transition succeeds, all memory addresses accessed are in bounds -/
lemma transition_isSome_implies_all_memory_bounds
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → F p)
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → F p)
    (state : State (F p))
    (h : (femtoCairoMachineTransition program memory state).isSome) :
    ∃ raw decode,
      fetchInstruction program state.pc = some raw ∧
      decodeInstruction raw.rawInstrType = some decode ∧
      (dataMemoryAccess memory raw.op1 decode.2.1 state.ap state.fp).isSome ∧
      (dataMemoryAccess memory raw.op2 decode.2.2.1 state.ap state.fp).isSome ∧
      (dataMemoryAccess memory raw.op3 decode.2.2.2 state.ap state.fp).isSome := by
  obtain ⟨raw, decode, v1, v2, v3, h_fetch, h_decode, h_v1, h_v2, h_v3, _⟩ :=
    transition_isSome_implies_computeNextState_isSome program memory state h
  exact ⟨raw, decode, h_fetch, h_decode,
    Option.isSome_iff_exists.mpr ⟨v1, h_v1⟩,
    Option.isSome_iff_exists.mpr ⟨v2, h_v2⟩,
    Option.isSome_iff_exists.mpr ⟨v3, h_v3⟩⟩

omit p_large_enough in
/-- If fetchInstruction succeeds, rawInstrType is a valid program memory value -/
lemma fetchInstruction_rawInstrType_eq_program
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → F p)
    (pc : F p) (raw : Types.RawInstruction (F p))
    (h : fetchInstruction program pc = some raw)
    (h_bound : pc.val < programSize) :
    raw.rawInstrType = program ⟨pc.val, h_bound⟩ := by
  simp only [fetchInstruction, Option.bind_eq_bind] at h
  cases h_mem : memoryAccess program pc with
  | none => simp [h_mem] at h
  | some type =>
    simp only [h_mem, Option.bind_some] at h
    simp only [memoryAccess] at h_mem
    split at h_mem
    case isTrue h_lt =>
      simp only [Option.some.injEq] at h_mem
      -- Extract remaining components
      cases h_op1 : memoryAccess program (pc + 1)
      · simp [h_op1] at h
      · simp only [h_op1, Option.bind_some] at h
        cases h_op2 : memoryAccess program (pc + 2)
        · simp [h_op2] at h
        · simp only [h_op2, Option.bind_some] at h
          cases h_op3 : memoryAccess program (pc + 3)
          · simp [h_op3] at h
          · simp only [h_op3, Option.bind_some, Option.some.injEq] at h
            -- h : { rawInstrType := type, op1 := .., op2 := .., op3 := .. } = raw
            -- h_mem : program ⟨h_lt, _⟩ = type
            -- Goal: raw.rawInstrType = program ⟨pc.val, h_bound⟩
            -- Lean sees proof irrelevance for Fin indices, so this closes the goal
            rw [← h, ← h_mem]
    case isFalse h_neg =>
      -- h_neg : ¬ pc.val < programSize, but we have h_bound : pc.val < programSize
      exact absurd h_bound h_neg

omit p_large_enough in
/-- Combining ValidProgram with fetchInstruction success gives rawInstrType.val < 256 -/
lemma fetchInstruction_rawInstrType_bound
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → F p)
    (h_valid : ValidProgram program)
    (pc : F p) (raw : Types.RawInstruction (F p))
    (h : fetchInstruction program pc = some raw)
    (h_bound : pc.val < programSize) :
    raw.rawInstrType.val < 256 := by
  rw [fetchInstruction_rawInstrType_eq_program program pc raw h h_bound]
  exact h_valid ⟨pc.val, h_bound⟩

end Examples.FemtoCairo.Spec
