/-
PicoCairoMultiplicity MUL Instruction Circuit
Following the same pattern as AddInstruction but for multiplication.
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

namespace Examples.PicoCairoMultiplicity.MulInstruction

open Examples.FemtoCairo
open Examples.FemtoCairo.Types
open Examples.FemtoCairo.Spec
open Examples.PicoCairoMultiplicity.Types
open Examples.PicoCairoMultiplicity.Helpers

variable {p : ℕ} [Fact p.Prime] [p_large_enough: Fact (p > 512)]

/--
Main circuit for MUL instruction step.
Takes enabled flag and pre-state.
If enabled, executes the MUL instruction and emits multiplicity operations.
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

  -- Step 4: Conditionally decode the instruction (returns dummy MUL when disabled)
  let decoded ← subcircuitWithAssertion conditionalDecodeCircuit {
    enabled := enabled,
    rawInstrType := rawInstruction.rawInstrType,
    dummy := dummyMULInstruction
  }

  -- Step 5: Unconditionally assert it's a MUL instruction
  -- When enabled=1, this checks the actual instruction is MUL
  -- When enabled=0, this always passes since dummy is MUL
  assertZero (decoded.instrType.isMul - 1)

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

  -- Step 7: Conditional MUL constraint: v3 = v1 * v2 (only when enabled)
  assertZero (enabled * (v3 - (v1 * v2)))

  -- Step 8: Compute next state (pc increments by 4, ap and fp unchanged for MUL)
  let postState : Var State (F p) := {
    pc := preState.pc + 4,
    ap := preState.ap,
    fp := preState.fp
  }

  -- Step 9: Conditionally emit +1 for post-state (producing)
  emitStateWhen enabled 1 postState

/--
ElaboratedCircuit for MUL instruction step.
-/
def elaborated
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → (F p)) (h_programSize : programSize < p)
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → (F p)) (h_memorySize : memorySize < p) :
    ElaboratedCircuit (F p) InstructionStepInput unit where
  main := main program h_programSize memory h_memorySize
  -- assertBool(0) + emitStateWhen(0) + fetchInstruction(4) + conditionalDecode(8) + assertZero(0) + 3×readMemory(5) + assertZero(0) + emitStateWhen(0) = 27
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
Assumptions for the MUL instruction step.
-/
def Assumptions
    {programSize : ℕ} [NeZero programSize]
    (input : InstructionStepInput (F p)) : Prop :=
  IsBool input.enabled ∧
  ZMod.val input.preState.pc + 3 < programSize

/--
Specification for the MUL instruction step.
If enabled, the pre-state consumed and post-state produced must reflect a valid MUL execution.
-/
def Spec
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → (F p))
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → (F p))
    (input : InstructionStepInput (F p)) (adds : InteractionDelta (F p)) : Prop :=
  if input.enabled = 1 then
    -- When enabled, we need to verify:
    -- 1. The pre-state is consumed (multiplicity -1)
    -- 2. The post-state is produced (multiplicity +1)
    -- 3. The MUL operation is valid according to FemtoCairo spec
    match Spec.fetchInstruction program input.preState.pc with
    | some rawInstr =>
      match Spec.decodeInstruction rawInstr.rawInstrType with
      | some (instrType, mode1, mode2, mode3) =>
        if instrType = 1 then  -- Must be MUL
          match Spec.dataMemoryAccess memory rawInstr.op1 mode1 input.preState.ap input.preState.fp,
                Spec.dataMemoryAccess memory rawInstr.op2 mode2 input.preState.ap input.preState.fp,
                Spec.dataMemoryAccess memory rawInstr.op3 mode3 input.preState.ap input.preState.fp with
          | some v1, some v2, some v3 =>
            v1 * v2 = v3 ∧
            adds = InteractionDelta.single ⟨"state", [input.preState.pc, input.preState.ap, input.preState.fp]⟩ (-1) +
                   InteractionDelta.single ⟨"state", [input.preState.pc + 4, input.preState.ap, input.preState.fp]⟩ 1
          | _, _, _ => False
        else False
      | none => False
    | none => False
  else
    -- When disabled, both entries have multiplicity 0, semantically equivalent to empty
    adds.toFinsupp = 0

/--
FormalAssertionChangingMultiset for the MUL instruction step.
-/
def circuit
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
    obtain ⟨_, h_fetch, h_decode_cond, h_isMul, h_read1, h_read2, h_read3, h_mul_constraint⟩ := h_holds

    -- Case split on enabled
    rcases h_enabled_bool with h_zero | h_one
    · -- Case: enabled = 0
      simp only [h_zero, zero_ne_one, ite_false, zero_mul, circuit_norm]
      exact InteractionDelta.toFinsupp_zero_mult _ _
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
        simp only [Option.some.injEq, one_mul, mul_one, circuit_norm]

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

          -- Show instrType = 1 from h_isMul constraint
          -- For MUL instruction: we need to show instr_type = 1
          -- Unlike ADD where isAdd=1 directly gives val=0,
          -- for MUL we need isAdd≠1 and isMul=1 to get val=1
          -- This requires case analysis on the one-hot encoding
          have h_isMul_eq : instr_type = 1 := by
            have h_isMul_1 := add_neg_eq_zero.mp h_isMul
            simp only [circuit_norm, explicit_provable_type] at h_isMul_1 h_instr_type h_instr_encoded
            simp only [DecodedInstructionType.isEncodedCorrectly, circuit_norm] at h_instr_encoded
            -- h_instr_encoded is now a 4-way Or
            -- h_isMul_1 says env.get (i₀ + 4 + 2) = 1 (isMul field)
            -- Only case 2 (isAdd=0, isMul=1) is consistent
            rcases h_instr_encoded with ⟨h1, h2, _, _⟩ | ⟨h1, h2, _, _⟩ | ⟨h1, h2, _, _⟩ | ⟨h1, h2, _, _⟩
            -- Case 1: isAdd=1, isMul=0 - h2 says isMul=0, contradicts h_isMul_1 (isMul=1)
            · rw [h2] at h_isMul_1; exact (one_ne_zero h_isMul_1.symm).elim
            -- Case 2: isAdd=0, isMul=1 - valid case
            · simp only [DecodedInstructionType.val, h1, zero_ne_one, ↓reduceIte, h_isMul_1] at h_instr_type
              exact h_instr_type.symm
            -- Case 3: isStoreState=1, isMul=0 - h2 says isMul=0, contradicts h_isMul_1
            · rw [h2] at h_isMul_1; exact (one_ne_zero h_isMul_1.symm).elim
            -- Case 4: isLoadState=1, isMul=0 - h2 says isMul=0, contradicts h_isMul_1
            · rw [h2] at h_isMul_1; exact (one_ne_zero h_isMul_1.symm).elim
          simp only [h_isMul_eq, ite_true]

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
            -- v1 * v2 = v3 from MUL constraint
            simp only [h_one, one_mul] at h_mul_constraint
            -- Get values from h_read hypotheses
            split at h_read1
            case h_1 val1 h_read1_val =>
              split at h_read2
              case h_1 val2 h_read2_val =>
                split at h_read3
                case h_1 val3 h_read3_val =>
                  have hv1 : v1 = val1 := by simp_all
                  have hv2 : v2 = val2 := by simp_all
                  have hv3 : v3 = val3 := by simp_all
                  rw [hv1, hv2, hv3, ←h_read1, ←h_read2, ←h_read3]
                  -- h_mul_constraint: v3 + -(v1 * v2) = 0 means v3 = v1 * v2
                  have h := h_mul_constraint
                  have h' : env.get (i₀ + 4 + 8 + 5 + 5 + 1 + 1 + 1 + 1) =
                            env.get (i₀ + 4 + 8 + 1 + 1 + 1 + 1) * env.get (i₀ + 4 + 8 + 5 + 1 + 1 + 1 + 1) := by
                    have : env.get (i₀ + 4 + 8 + 5 + 5 + 1 + 1 + 1 + 1) +
                           -(env.get (i₀ + 4 + 8 + 1 + 1 + 1 + 1) * env.get (i₀ + 4 + 8 + 5 + 1 + 1 + 1 + 1)) = 0 := h
                    have := add_neg_eq_zero.mp this
                    exact this
                  ring_nf at h' ⊢
                  exact h'.symm
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
Bundle of MUL instruction step circuits.
Takes a vector of inputs with given capacity and executes MUL instructions for each enabled input.
-/
def main
    (capacity : ℕ) [NeZero capacity]
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → (F p)) (h_programSize : programSize < p)
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → (F p)) (h_memorySize : memorySize < p)
    (inputs : Var (ProvableVector InstructionStepInput capacity) (F p)) : Circuit (F p) Unit := do
  for h : i in [0:capacity] do
    let idx : Fin capacity := ⟨i, Membership.mem.upper h⟩
    (MulInstruction.circuit program h_programSize memory h_memorySize).elaborated.main inputs[idx.val]

/--
Elaborated circuit for MUL instruction bundle.
-/
def elaborated
    (capacity : ℕ) [NeZero capacity]
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → (F p)) (h_programSize : programSize < p)
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → (F p)) (h_memorySize : memorySize < p) :
    ElaboratedCircuit (F p) (ProvableVector InstructionStepInput capacity) unit where
  main := main capacity program h_programSize memory h_memorySize
  localLength _ := capacity * 27
  localLength_eq := by sorry
  output _ _ := ()
  localAdds inputs env offset :=
    -- Sum up localAdds from each instruction step using list fold
    (List.finRange capacity).foldl (fun acc i =>
      let input := eval env inputs[i]
      let preState := input.preState
      let postState : State (F p) := { pc := preState.pc + 4, ap := preState.ap, fp := preState.fp }
      let enabled := input.enabled
      acc +
      InteractionDelta.single ⟨"state", [preState.pc, preState.ap, preState.fp]⟩ (enabled * (-1)) +
      InteractionDelta.single ⟨"state", [postState.pc, postState.ap, postState.fp]⟩ (enabled * 1)
    ) 0
  localAdds_eq := by sorry
  subcircuitsConsistent := by sorry

def Assumptions
    (capacity : ℕ) [NeZero capacity]
    {programSize : ℕ} [NeZero programSize]
    (inputs : ProvableVector InstructionStepInput capacity (F p)) : Prop :=
  ∀ i : Fin capacity, MulInstruction.Assumptions (programSize := programSize) inputs[i]

def Spec
    (capacity : ℕ) [NeZero capacity]
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → (F p))
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → (F p))
    (inputs : ProvableVector InstructionStepInput capacity (F p))
    (adds : InteractionDelta (F p)) : Prop :=
  ∃ (stepAdds : Fin capacity → InteractionDelta (F p)),
    (∀ i : Fin capacity, MulInstruction.Spec program memory inputs[i] (stepAdds i)) ∧
    adds = (List.finRange capacity).foldl (fun acc i => acc + stepAdds i) 0

def circuit
    (capacity : ℕ) [NeZero capacity]
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → (F p)) (h_programSize : programSize < p)
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → (F p)) (h_memorySize : memorySize < p) :
    FormalAssertionChangingMultiset (F p) (ProvableVector InstructionStepInput capacity) where
  elaborated := elaborated capacity program h_programSize memory h_memorySize
  Assumptions := Assumptions capacity (programSize := programSize)
  Spec := Spec capacity program memory
  soundness := by sorry
  completeness := by sorry

end Bundle

end Examples.PicoCairoMultiplicity.MulInstruction
