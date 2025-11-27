/-
PicoCairoMultiplicity LOAD_STATE Instruction Circuit
Following the same pattern as AddInstruction but for loading state.
LOAD_STATE reads v1, v2, v3 from memory and sets pc=v1, ap=v2, fp=v3.
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

namespace Examples.PicoCairoMultiplicity.LoadStateInstruction

open Examples.FemtoCairo
open Examples.FemtoCairo.Types
open Examples.FemtoCairo.Spec
open Examples.PicoCairoMultiplicity.Types
open Examples.PicoCairoMultiplicity.Helpers
open Operations (collectAdds collectAdds_flatten collectAdds_ofFn_flatten)
open Circuit (collectAdds_forEach_foldl)

variable {p : ℕ} [Fact p.Prime] [p_large_enough: Fact (p > 512)]

/--
Main circuit for LOAD_STATE instruction step.
Takes enabled flag and pre-state.
If enabled, executes the LOAD_STATE instruction and emits multiplicity operations.
LOAD_STATE loads a new state from memory: pc := v1, ap := v2, fp := v3.
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

  -- Step 4: Conditionally decode the instruction (returns dummy LOAD_STATE when disabled)
  let decoded ← subcircuitWithAssertion conditionalDecodeCircuit {
    enabled := enabled,
    rawInstrType := rawInstruction.rawInstrType,
    dummy := dummyLoadStateInstruction
  }

  -- Step 5: Unconditionally assert it's a LOAD_STATE instruction
  -- When enabled=1, this checks the actual instruction is LOAD_STATE
  -- When enabled=0, this always passes since dummy is LOAD_STATE
  assertZero (decoded.instrType.isLoadState - 1)

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

  -- Step 7: No arithmetic constraint for LOAD_STATE
  -- The state transition is determined by the memory values

  -- Step 8: Compute next state (pc := v1, ap := v2, fp := v3)
  let postState : Var State (F p) := {
    pc := v1,
    ap := v2,
    fp := v3
  }

  -- Step 9: Conditionally emit +1 for post-state (producing)
  emitStateWhen enabled 1 postState

/--
ElaboratedCircuit for LOAD_STATE instruction step.
-/
def elaborated
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → (F p)) (h_programSize : programSize < p)
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → (F p)) (h_memorySize : memorySize < p) :
    ElaboratedCircuit (F p) InstructionStepInput unit where
  main := main program h_programSize memory h_memorySize
  -- assertBool(0) + emitStateWhen(0) + fetchInstruction(4) + conditionalDecode(8) + assertZero(0) + 3×readMemory(5) + emitStateWhen(0) = 27
  localLength _ := 27
  output _ _ := ()
  localAdds input env offset :=
    let preState := eval env input.preState
    -- For LOAD_STATE, postState uses the memory values v1, v2, v3
    -- These are at offsets: v1 at i₀+4+8+4, v2 at i₀+4+8+5+4, v3 at i₀+4+8+5+5+4
    let v1 := env.get (offset + 4 + 8 + 4)
    let v2 := env.get (offset + 4 + 8 + 5 + 4)
    let v3 := env.get (offset + 4 + 8 + 5 + 5 + 4)
    let postState : State (F p) := {
      pc := v1,
      ap := v2,
      fp := v3
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
Assumptions for the LOAD_STATE instruction step.
-/
def Assumptions
    {programSize : ℕ} [NeZero programSize]
    (input : InstructionStepInput (F p)) : Prop :=
  IsBool input.enabled ∧
  ZMod.val input.preState.pc + 3 < programSize

/--
Specification for the LOAD_STATE instruction step.
If enabled, the pre-state consumed and post-state produced must reflect a valid LOAD_STATE execution.
-/
def Spec
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → (F p))
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → (F p))
    (input : InstructionStepInput (F p)) (adds : InteractionDelta (F p)) : Prop :=
  if input.enabled = 1 then
    -- When enabled, we need to verify:
    -- 1. The pre-state is consumed (multiplicity -1)
    -- 2. The post-state is produced (multiplicity +1)
    -- 3. The LOAD_STATE operation is valid according to FemtoCairo spec
    match Spec.fetchInstruction program input.preState.pc with
    | some rawInstr =>
      match Spec.decodeInstruction rawInstr.rawInstrType with
      | some (instrType, mode1, mode2, mode3) =>
        if instrType = 3 then  -- Must be LOAD_STATE
          match Spec.dataMemoryAccess memory rawInstr.op1 mode1 input.preState.ap input.preState.fp,
                Spec.dataMemoryAccess memory rawInstr.op2 mode2 input.preState.ap input.preState.fp,
                Spec.dataMemoryAccess memory rawInstr.op3 mode3 input.preState.ap input.preState.fp with
          | some v1, some v2, some v3 =>
            -- LOAD_STATE: new state is (v1, v2, v3)
            adds = InteractionDelta.single ⟨"state", [input.preState.pc, input.preState.ap, input.preState.fp]⟩ (-1) +
                   InteractionDelta.single ⟨"state", [v1, v2, v3]⟩ 1
          | _, _, _ => False
        else False
      | none => False
    | none => False
  else
    -- When disabled, both entries have multiplicity 0, semantically equivalent to empty
    adds.toFinsupp = 0

/--
FormalAssertionChangingMultiset for the LOAD_STATE instruction step.
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
    obtain ⟨_, h_fetch, h_decode_cond, h_isLoadState, h_read1, h_read2, h_read3⟩ := h_holds

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

          -- Show instrType = 3 from h_isLoadState constraint
          have h_isLoadState_eq : instr_type = 3 := by
            have h_isLoadState_1 := add_neg_eq_zero.mp h_isLoadState
            simp only [circuit_norm, explicit_provable_type] at h_isLoadState_1 h_instr_type h_instr_encoded
            simp only [DecodedInstructionType.isEncodedCorrectly, circuit_norm] at h_instr_encoded
            rcases h_instr_encoded with ⟨h1, _, _, h4⟩ | ⟨_, _, _, h4⟩ | ⟨_, _, _, h4⟩ | ⟨h1, h2, h3, h4⟩
            -- Case 1: isAdd=1, isLoadState=0 - h4 says isLoadState=0, contradicts h_isLoadState_1 (isLoadState=1)
            · rw [h4] at h_isLoadState_1; exact (one_ne_zero h_isLoadState_1.symm).elim
            -- Case 2: isMul=1, isLoadState=0 - contradicts h_isLoadState_1
            · rw [h4] at h_isLoadState_1; exact (one_ne_zero h_isLoadState_1.symm).elim
            -- Case 3: isStoreState=1, isLoadState=0 - contradicts h_isLoadState_1
            · rw [h4] at h_isLoadState_1; exact (one_ne_zero h_isLoadState_1.symm).elim
            -- Case 4: isLoadState=1 - valid case
            · simp only [DecodedInstructionType.val, h1, zero_ne_one, ↓reduceIte, h2, h3, h_isLoadState_1] at h_instr_type
              exact h_instr_type.symm
          simp only [h_isLoadState_eq, ite_true]

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
            -- For LOAD_STATE, the goal is just to show adds equality
            split at h_read1
            case h_1 val1 h_read1_val =>
              split at h_read2
              case h_1 val2 h_read2_val =>
                split at h_read3
                case h_1 val3 h_read3_val =>
                  have hv1 : v1 = val1 := by simp_all
                  have hv2 : v2 = val2 := by simp_all
                  have hv3 : v3 = val3 := by simp_all
                  simp only [hv1, hv2, hv3, ←h_read1, ←h_read2, ←h_read3]
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
Step body for a single LOAD_STATE instruction in the bundle.
-/
def stepBody
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → (F p)) (h_programSize : programSize < p)
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → (F p)) (h_memorySize : memorySize < p)
    (input : Var InstructionStepInput (F p)) : Circuit (F p) Unit :=
  (LoadStateInstruction.circuit program h_programSize memory h_memorySize).elaborated.main input

instance stepBody_constantLength
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → (F p)) (h_programSize : programSize < p)
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → (F p)) (h_memorySize : memorySize < p) :
    Circuit.ConstantLength (stepBody program h_programSize memory h_memorySize) where
  localLength := 27
  localLength_eq _ _ := by
    simp only [stepBody]
    exact (LoadStateInstruction.circuit program h_programSize memory h_memorySize).elaborated.localLength_eq _ _

/--
Main circuit for executing a bundle of LOAD_STATE instructions.
-/
def main
    (capacity : ℕ) [NeZero capacity]
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → (F p)) (h_programSize : programSize < p)
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → (F p)) (h_memorySize : memorySize < p)
    (inputs : Var (ProvableVector InstructionStepInput capacity) (F p)) : Circuit (F p) Unit :=
  Circuit.forEach inputs (stepBody program h_programSize memory h_memorySize)
    (stepBody_constantLength program h_programSize memory h_memorySize)

/--
ElaboratedCircuit for the LOAD_STATE bundle.
-/
def elaborated
    (capacity : ℕ) [NeZero capacity]
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → (F p)) (h_programSize : programSize < p)
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → (F p)) (h_memorySize : memorySize < p) :
    ElaboratedCircuit (F p) (ProvableVector InstructionStepInput capacity) unit where
  main := main capacity program h_programSize memory h_memorySize
  localLength _ := capacity * 27
  localLength_eq := by
    intros input offset
    simp only [main, Circuit.forEach.localLength_eq]
    congr 1
  output _ _ := ()
  localAdds inputs env offset :=
    (List.finRange capacity).foldl (fun acc (i : Fin capacity) =>
      let input := eval env inputs[i]
      let preState := input.preState
      -- For LOAD_STATE, postState uses the memory values v1, v2, v3 at computed offsets
      let v1 := env.get (offset + i * 27 + 4 + 8 + 4)
      let v2 := env.get (offset + i * 27 + 4 + 8 + 5 + 4)
      let v3 := env.get (offset + i * 27 + 4 + 8 + 5 + 5 + 4)
      let postState : State (F p) := { pc := v1, ap := v2, fp := v3 }
      let enabled := input.enabled
      acc +
      InteractionDelta.single ⟨"state", [preState.pc, preState.ap, preState.fp]⟩ (enabled * (-1)) +
      InteractionDelta.single ⟨"state", [postState.pc, postState.ap, postState.fp]⟩ (enabled * 1)
    ) 0
  localAdds_eq inputs env offset := by
    -- Unfold main to expose forEach
    simp only [main]
    -- Use collectAdds_forEach_foldl to rewrite LHS
    rw [collectAdds_forEach_foldl]
    -- Convert both foldls to sums using toFinsupp_foldl_finRange
    rw [InteractionDelta.toFinsupp_foldl_finRange]
    simp only [add_assoc]
    rw [InteractionDelta.toFinsupp_foldl_finRange]
    -- Now prove term-by-term equality
    apply Finset.sum_congr rfl
    intro i _
    -- Unfold stepBody and localLength
    simp only [stepBody, Circuit.ConstantLength.localLength, stepBody_constantLength]
    -- Use LoadStateInstruction.elaborated.localAdds_eq
    have h_step := (LoadStateInstruction.elaborated program h_programSize memory h_memorySize).localAdds_eq
      inputs[i] env (offset + ↑i * 27)
    rw [Circuit.operations] at h_step
    rw [h_step]
    -- The LHS is now LoadStateInstruction.elaborated.localAdds which equals the RHS by definition
    simp only [ElaboratedCircuit.localAdds, LoadStateInstruction.elaborated, circuit_norm]
    rfl
  subcircuitsConsistent := by
    intros inputs offset
    rw [Operations.SubcircuitsConsistent, main, Circuit.forEach.forAll]
    intro i
    exact (LoadStateInstruction.elaborated program h_programSize memory h_memorySize).subcircuitsConsistent _ _

/--
Assumptions for the LOAD_STATE bundle.
-/
def Assumptions
    (capacity : ℕ) [NeZero capacity]
    {programSize : ℕ} [NeZero programSize]
    (inputs : ProvableVector InstructionStepInput capacity (F p)) : Prop :=
  ∀ i : Fin capacity, LoadStateInstruction.Assumptions (programSize := programSize) inputs[i.val]

/--
Specification for the LOAD_STATE bundle.
-/
def Spec
    (capacity : ℕ) [NeZero capacity]
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → (F p))
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → (F p))
    (inputs : ProvableVector InstructionStepInput capacity (F p)) (adds : InteractionDelta (F p)) : Prop :=
  ∃ individualAdds : Fin capacity → InteractionDelta (F p),
    (∀ i, LoadStateInstruction.Spec program memory inputs[i.val] (individualAdds i)) ∧
    adds = List.foldl (· + ·) 0 (List.ofFn individualAdds)

/--
FormalAssertionChangingMultiset for the LOAD_STATE bundle.
-/
def circuit
    (capacity : ℕ) [NeZero capacity]
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → (F p)) (h_programSize : programSize < p)
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → (F p)) (h_memorySize : memorySize < p) :
    FormalAssertionChangingMultiset (F p) (ProvableVector InstructionStepInput capacity) where
  elaborated := elaborated capacity program h_programSize memory h_memorySize
  Assumptions := Assumptions capacity (programSize := programSize)
  Spec := Spec capacity program memory
  soundness := by
    intro offset env inputs_var inputs h_eval h_assumptions h_holds
    simp only [elaborated, main] at h_holds
    rw [Circuit.forEach.soundness] at h_holds
    -- Define stepAdds inline with the LoadState-specific postState
    use fun i =>
      let input := inputs_var[i]
      let preState := eval env input.preState
      -- LoadState uses memory reads for postState
      let v1 := env.get (offset + i * 27 + 4 + 8 + 4)
      let v2 := env.get (offset + i * 27 + 4 + 8 + 5 + 4)
      let v3 := env.get (offset + i * 27 + 4 + 8 + 5 + 5 + 4)
      let postState : State (F p) := { pc := v1, ap := v2, fp := v3 }
      let enabled := input.enabled.eval env
      InteractionDelta.single ⟨"state", [preState.pc, preState.ap, preState.fp]⟩ (enabled * (-1)) +
      InteractionDelta.single ⟨"state", [postState.pc, postState.ap, postState.fp]⟩ (enabled * 1)
    constructor
    · -- Each step satisfies LoadStateInstruction.Spec
      intro i
      sorry
    · -- The adds sum correctly
      simp only [elaborated, Spec]
      -- Convert List.ofFn to List.finRange foldl form
      sorry
  completeness := by
    sorry

end Bundle

end Examples.PicoCairoMultiplicity.LoadStateInstruction
