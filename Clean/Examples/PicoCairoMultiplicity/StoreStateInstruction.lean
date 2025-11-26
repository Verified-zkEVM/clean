/-
PicoCairoMultiplicity STORE_STATE Instruction Circuit
Following the same pattern as AddInstruction but for storing state.
STORE_STATE checks that v1=pc, v2=ap, v3=fp (i.e., the state is stored in memory).
-/

import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Circuit.Loops
import Clean.Examples.PicoCairoMultiplicity.Types
import Clean.Examples.PicoCairoMultiplicity.Helpers
import Clean.Examples.FemtoCairo.FemtoCairo
import Clean.Examples.FemtoCairo.Types
import Clean.Examples.FemtoCairo.Spec
import Clean.Gadgets.Boolean
import Batteries.Data.Vector.Lemmas

namespace Examples.PicoCairoMultiplicity.StoreStateInstruction

open Examples.FemtoCairo
open Examples.FemtoCairo.Types
open Examples.FemtoCairo.Spec
open Examples.PicoCairoMultiplicity.Types
open Examples.PicoCairoMultiplicity.Helpers

variable {p : ℕ} [Fact p.Prime] [p_large_enough: Fact (p > 512)]

/--
Main circuit for STORE_STATE instruction step.
Takes enabled flag and pre-state.
If enabled, executes the STORE_STATE instruction and emits multiplicity operations.
STORE_STATE checks that v1=pc, v2=ap, v3=fp (the state is stored in memory).
-/
def main
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → (F p)) (h_programSize : programSize < p)
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → (F p)) (h_memorySize : memorySize < p)
    (input : Var InstructionStepInput (F p)) : Circuit (F p) Unit := do

  let enabled := input.enabled
  let preState := input.preState

  -- Step 1: Assert enabled is boolean (0 or 1)
  assertBool enabled

  -- Step 2: Conditionally emit -1 for pre-state (consuming)
  emitStateWhen enabled (-1) preState

  -- Step 3: Fetch instruction from program memory
  let rawInstruction ← subcircuitWithAssertion (fetchInstructionCircuit program h_programSize) preState.pc

  -- Step 4: Conditionally decode the instruction (returns dummy STORE_STATE when disabled)
  let decoded ← subcircuitWithAssertion conditionalDecodeCircuit {
    enabled := enabled,
    rawInstrType := rawInstruction.rawInstrType,
    dummy := dummyStoreStateInstruction
  }

  -- Step 5: Unconditionally assert it's a STORE_STATE instruction
  -- When enabled=1, this checks the actual instruction is STORE_STATE
  -- When enabled=0, this always passes since dummy is STORE_STATE
  assertZero (decoded.instrType.isStoreState - 1)

  -- Step 6: Read operands from memory using addressing modes
  let v1 ← subcircuitWithAssertion (readFromMemoryCircuit memory h_memorySize) {
    state := preState,
    offset := rawInstruction.op1,
    mode := decoded.mode1
  }

  let v2 ← subcircuitWithAssertion (readFromMemoryCircuit memory h_memorySize) {
    state := preState,
    offset := rawInstruction.op2,
    mode := decoded.mode2
  }

  let v3 ← subcircuitWithAssertion (readFromMemoryCircuit memory h_memorySize) {
    state := preState,
    offset := rawInstruction.op3,
    mode := decoded.mode3
  }

  -- Step 7: STORE_STATE constraint: v1 = pc, v2 = ap, v3 = fp (only when enabled)
  assertZero (enabled * (v1 - preState.pc))
  assertZero (enabled * (v2 - preState.ap))
  assertZero (enabled * (v3 - preState.fp))

  -- Step 8: Compute next state (pc increments by 4, ap and fp unchanged for STORE_STATE)
  let postState : Var State (F p) := {
    pc := preState.pc + 4,
    ap := preState.ap,
    fp := preState.fp
  }

  -- Step 9: Conditionally emit +1 for post-state (producing)
  emitStateWhen enabled 1 postState

/--
ElaboratedCircuit for STORE_STATE instruction step.
-/
noncomputable def elaborated
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → (F p)) (h_programSize : programSize < p)
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → (F p)) (h_memorySize : memorySize < p) :
    ElaboratedCircuit (F p) InstructionStepInput unit where
  main := main program h_programSize memory h_memorySize
  -- assertBool(0) + emitStateWhen(0) + fetchInstruction(4) + conditionalDecode(8) + assertZero(0) + 3×readMemory(5) + 3×assertZero(0) + emitStateWhen(0) = 27
  localLength _ := 27
  output _ _ := ()
  localAdds input env offset :=
    let preState := eval env input.preState
    let postState : State (F p) := {
      pc := preState.pc + 4,
      ap := preState.ap,
      fp := preState.fp
    }
    let enabled := input.enabled.eval env
    InteractionDelta.single ⟨"state", [preState.pc, preState.ap, preState.fp]⟩ (enabled * (-1)) +
    InteractionDelta.single ⟨"state", [postState.pc, postState.ap, postState.fp]⟩ (enabled * 1)
  localAdds_eq := by
    intro input env offset
    simp only [main, circuit_norm, emitStateWhen, emitAdd, fetchInstructionCircuit,
      conditionalDecodeCircuit, conditionalDecodeElaborated, conditionalDecodeMain,
      readFromMemoryCircuit, assertBool, FormalAssertion.toSubcircuit,
      Operations.collectAdds, List.nil_append, NamedList.eval,
      add_zero, zero_add]
    rfl

/--
Assumptions for the STORE_STATE instruction step.
-/
def Assumptions
    {programSize : ℕ} [NeZero programSize]
    (input : InstructionStepInput (F p)) : Prop :=
  IsBool input.enabled ∧
  ZMod.val input.preState.pc + 3 < programSize

/--
Specification for the STORE_STATE instruction step.
If enabled, the pre-state consumed and post-state produced must reflect a valid STORE_STATE execution.
-/
def Spec
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → (F p))
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → (F p))
    (input : InstructionStepInput (F p)) (adds : InteractionDelta (F p)) : Prop :=
  if input.enabled = 1 then
    -- When enabled, we need to verify:
    -- 1. The pre-state is consumed (multiplicity -1)
    -- 2. The post-state is produced (multiplicity +1)
    -- 3. The STORE_STATE operation is valid according to FemtoCairo spec
    match Spec.fetchInstruction program input.preState.pc with
    | some rawInstr =>
      match Spec.decodeInstruction rawInstr.rawInstrType with
      | some (instrType, mode1, mode2, mode3) =>
        if instrType = 2 then  -- Must be STORE_STATE
          match Spec.dataMemoryAccess memory rawInstr.op1 mode1 input.preState.ap input.preState.fp,
                Spec.dataMemoryAccess memory rawInstr.op2 mode2 input.preState.ap input.preState.fp,
                Spec.dataMemoryAccess memory rawInstr.op3 mode3 input.preState.ap input.preState.fp with
          | some v1, some v2, some v3 =>
            -- STORE_STATE: verify v1=pc, v2=ap, v3=fp
            v1 = input.preState.pc ∧ v2 = input.preState.ap ∧ v3 = input.preState.fp ∧
            adds = InteractionDelta.single ⟨"state", [input.preState.pc, input.preState.ap, input.preState.fp]⟩ (-1) +
                   InteractionDelta.single ⟨"state", [input.preState.pc + 4, input.preState.ap, input.preState.fp]⟩ 1
          | _, _, _ => False
        else False
      | none => False
    | none => False
  else
    -- When disabled, both entries have multiplicity 0
    adds = 0  -- Empty delta when disabled

/--
FormalAssertionChangingMultiset for the STORE_STATE instruction step.
-/
noncomputable def circuit
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → (F p)) (h_programSize : programSize < p)
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → (F p)) (h_memorySize : memorySize < p) :
    FormalAssertionChangingMultiset (F p) InstructionStepInput where
  elaborated := elaborated program h_programSize memory h_memorySize
  Assumptions := Assumptions (programSize := programSize)
  Spec := Spec program memory
  soundness := by
    circuit_proof_start [elaborated, main, Assumptions, Spec, fetchInstructionCircuit,
      conditionalDecodeCircuit, conditionalDecodeElaborated, conditionalDecodeMain,
      readFromMemoryCircuit, decodeInstructionCircuit, decodeInstructionSpec]

    -- Extract assumptions
    obtain ⟨h_enabled_bool, h_pc_bound⟩ := h_assumptions
    obtain ⟨h_input_enabled, h_input_preState⟩ := h_input

    -- Extract constraints from h_holds
    obtain ⟨_, h_fetch, h_decode_cond, h_isStoreState, h_read1, h_read2, h_read3,
            h_store_constraint1, h_store_constraint2, h_store_constraint3⟩ := h_holds

    -- Case split on enabled
    rcases h_enabled_bool with h_zero | h_one
    · -- Case: enabled = 0
      simp only [h_zero, zero_ne_one, ite_false, zero_mul, circuit_norm]
    · -- Case: enabled = 1
      simp only [h_one, ite_true]

      -- Simplify h_input_preState to get eval relation on pc
      have h_pc_eval : Expression.eval env input_var_preState.pc = input_preState.pc := by
        rw [←h_input_preState]; rfl
      rw [h_pc_eval] at h_fetch

      -- Split on fetchInstruction result
      split at h_fetch
      case h_2 => contradiction
      case h_1 rawInstr h_fetch_eq =>
        rw [h_fetch_eq]
        simp only [one_mul, mul_one, circuit_norm]

        -- Get the decode result - apply IsBool hypothesis
        have h_bool : IsBool input_enabled := Or.inr h_one
        specialize h_decode_cond h_bool
        simp only [h_one, one_ne_zero, ite_false] at h_decode_cond

        -- Relate env.get i₀ to rawInstr.rawInstrType using h_fetch
        have h_rawInstrType : env.get i₀ = rawInstr.rawInstrType := congrArg RawInstruction.rawInstrType h_fetch
        have h_op1 : env.get (i₀ + 1) = rawInstr.op1 := congrArg RawInstruction.op1 h_fetch
        have h_op2 : env.get (i₀ + 1 + 1) = rawInstr.op2 := congrArg RawInstruction.op2 h_fetch
        have h_op3 : env.get (i₀ + 1 + 1 + 1) = rawInstr.op3 := congrArg RawInstruction.op3 h_fetch

        rw [h_rawInstrType] at h_decode_cond

        split at h_decode_cond
        case h_2 => exact h_decode_cond.elim
        case h_1 instr_type mode1_val mode2_val mode3_val h_decode_eq =>
          -- Rewrite goal with h_decode_eq
          simp only [h_decode_eq]
          obtain ⟨h_instr_type, h_instr_encoded, h_mode1, h_mode1_encoded,
                  h_mode2, h_mode2_encoded, h_mode3, h_mode3_encoded⟩ := h_decode_cond

          -- Show instrType = 2 from h_isStoreState constraint
          have h_isStoreState_eq : instr_type = 2 := by
            have h_isStoreState_1 := add_neg_eq_zero.mp h_isStoreState
            simp only [circuit_norm, explicit_provable_type] at h_isStoreState_1 h_instr_type h_instr_encoded
            simp only [DecodedInstructionType.isEncodedCorrectly, circuit_norm] at h_instr_encoded
            rcases h_instr_encoded with ⟨_, _, h3, _⟩ | ⟨_, _, h3, _⟩ | ⟨h1, h2, h3, h4⟩ | ⟨_, _, h3, _⟩
            -- Case 1: isAdd=1, isStoreState=0 - h3 says isStoreState=0, contradicts h_isStoreState_1
            · rw [h3] at h_isStoreState_1; exact (one_ne_zero h_isStoreState_1.symm).elim
            -- Case 2: isMul=1, isStoreState=0 - contradicts h_isStoreState_1
            · rw [h3] at h_isStoreState_1; exact (one_ne_zero h_isStoreState_1.symm).elim
            -- Case 3: isStoreState=1 - valid case
            · simp only [DecodedInstructionType.val, h1, zero_ne_one, ↓reduceIte, h2, h_isStoreState_1] at h_instr_type
              exact h_instr_type.symm
            -- Case 4: isLoadState=1, isStoreState=0 - contradicts h_isStoreState_1
            · rw [h3] at h_isStoreState_1; exact (one_ne_zero h_isStoreState_1.symm).elim
          simp only [h_isStoreState_eq, ite_true]

          -- Use soundness of memory reads
          specialize h_read1 h_mode1_encoded
          specialize h_read2 h_mode2_encoded
          specialize h_read3 h_mode3_encoded

          rw [h_mode1, h_op1] at h_read1
          rw [h_mode2, h_op2] at h_read2
          rw [h_mode3, h_op3] at h_read3

          -- Split on the goal's match expressions
          split
          case h_1 v1 v2 v3 h_v1_eq h_v2_eq h_v3_eq =>
            -- For STORE_STATE, prove v1=pc, v2=ap, v3=fp from constraints
            simp only [h_one, one_mul] at h_store_constraint1 h_store_constraint2 h_store_constraint3
            split at h_read1
            case h_1 val1 h_read1_val =>
              split at h_read2
              case h_1 val2 h_read2_val =>
                split at h_read3
                case h_1 val3 h_read3_val =>
                  have hv1 : v1 = val1 := by simp_all
                  have hv2 : v2 = val2 := by simp_all
                  have hv3 : v3 = val3 := by simp_all
                  -- Prove v1 = pc from h_store_constraint1
                  have h_ap_eval : Expression.eval env input_var_preState.ap = input_preState.ap := by
                    rw [←h_input_preState]; rfl
                  have h_fp_eval : Expression.eval env input_var_preState.fp = input_preState.fp := by
                    rw [←h_input_preState]; rfl
                  have h_v1_eq_pc : val1 = input_preState.pc := by
                    have h := add_neg_eq_zero.mp h_store_constraint1
                    rw [h_read1, h_pc_eval] at h
                    exact h
                  have h_v2_eq_ap : val2 = input_preState.ap := by
                    have h := add_neg_eq_zero.mp h_store_constraint2
                    rw [h_read2, h_ap_eval] at h
                    exact h
                  have h_v3_eq_fp : val3 = input_preState.fp := by
                    have h := add_neg_eq_zero.mp h_store_constraint3
                    rw [h_read3, h_fp_eval] at h
                    exact h
                  rw [hv1, hv2, hv3, h_v1_eq_pc, h_v2_eq_ap, h_v3_eq_fp]
                  exact ⟨rfl, rfl, rfl⟩
                case h_2 => simp_all
              case h_2 => simp_all
            case h_2 => simp_all
          case h_2 =>
            -- One of dataMemoryAccess returned none - show contradiction
            split at h_read1 <;> split at h_read2 <;> split at h_read3 <;> simp_all
  completeness := by
    sorry

namespace Bundle

/--
Main circuit for executing a bundle of STORE_STATE instructions.
-/
noncomputable def main
    (capacity : ℕ) [NeZero capacity]
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → (F p)) (h_programSize : programSize < p)
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → (F p)) (h_memorySize : memorySize < p)
    (inputs : Var (ProvableVector InstructionStepInput capacity) (F p)) : Circuit (F p) Unit := do
  for h : i in [0:capacity] do
    let idx : Fin capacity := ⟨i, Membership.mem.upper h⟩
    -- Use the circuit for compositional reuse
    (StoreStateInstruction.circuit program h_programSize memory h_memorySize).elaborated.main inputs[idx.val]

/--
ElaboratedCircuit for the STORE_STATE bundle.
-/
noncomputable def elaborated
    (capacity : ℕ) [NeZero capacity]
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → (F p)) (h_programSize : programSize < p)
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → (F p)) (h_memorySize : memorySize < p) :
    ElaboratedCircuit (F p) (ProvableVector InstructionStepInput capacity) unit where
  main := main capacity program h_programSize memory h_memorySize
  localLength _ := capacity * 27
  localLength_eq := by
    intro input offset
    sorry
  output _ _ := ()
  localAdds inputs env offset :=
    let inputsEval := eval env inputs
    List.foldl (· + ·) 0 <| List.ofFn fun (i : Fin capacity) =>
      let preState := inputsEval[i.val].preState
      let postState : State (F p) := {
        pc := preState.pc + 4,
        ap := preState.ap,
        fp := preState.fp
      }
      let enabled := inputsEval[i.val].enabled
      InteractionDelta.single ⟨"state", [preState.pc, preState.ap, preState.fp]⟩ (enabled * (-1)) +
      InteractionDelta.single ⟨"state", [postState.pc, postState.ap, postState.fp]⟩ (enabled * 1)
  localAdds_eq := by
    intro input env offset
    sorry
  subcircuitsConsistent := by
    intro input offset
    sorry

/--
Assumptions for the STORE_STATE bundle.
-/
def Assumptions
    (capacity : ℕ) [NeZero capacity]
    {programSize : ℕ} [NeZero programSize]
    (inputs : ProvableVector InstructionStepInput capacity (F p)) : Prop :=
  ∀ i : Fin capacity, StoreStateInstruction.Assumptions (programSize := programSize) inputs[i.val]

/--
Specification for the STORE_STATE bundle.
-/
def Spec
    (capacity : ℕ) [NeZero capacity]
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → (F p))
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → (F p))
    (inputs : ProvableVector InstructionStepInput capacity (F p)) (adds : InteractionDelta (F p)) : Prop :=
  ∃ individualAdds : Fin capacity → InteractionDelta (F p),
    (∀ i, StoreStateInstruction.Spec program memory inputs[i.val] (individualAdds i)) ∧
    adds = List.foldl (· + ·) 0 (List.ofFn individualAdds)

/--
FormalAssertionChangingMultiset for the STORE_STATE bundle.
-/
noncomputable def circuit
    (capacity : ℕ) [NeZero capacity]
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → (F p)) (h_programSize : programSize < p)
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → (F p)) (h_memorySize : memorySize < p) :
    FormalAssertionChangingMultiset (F p) (ProvableVector InstructionStepInput capacity) where
  elaborated := elaborated capacity program h_programSize memory h_memorySize
  Assumptions := Assumptions capacity (programSize := programSize)
  Spec := Spec capacity program memory
  soundness := by
    sorry
  completeness := by
    sorry

end Bundle

end Examples.PicoCairoMultiplicity.StoreStateInstruction
