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
  let rawInstruction ← subcircuitWithAssertion (fetchInstruction program h_programSize) preState.pc

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
  let v1 ← subcircuitWithAssertion (readFromMemory memory h_memorySize) {
    state := preState,
    offset := rawInstruction.op1,
    mode := decoded.mode1
  }

  let v2 ← subcircuitWithAssertion (readFromMemory memory h_memorySize) {
    state := preState,
    offset := rawInstruction.op2,
    mode := decoded.mode2
  }

  let v3 ← subcircuitWithAssertion (readFromMemory memory h_memorySize) {
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
    simp only [main, circuit_norm, emitStateWhen, emitAdd, FemtoCairo.fetchInstruction,
      conditionalDecodeCircuit, conditionalDecodeElaborated, conditionalDecodeMain,
      readFromMemory, assertBool, FormalAssertion.toSubcircuit,
      Operations.collectAdds, List.nil_append, NamedList.eval,
      add_zero]
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
    circuit_proof_start [elaborated, main, Assumptions, Spec, FemtoCairo.fetchInstruction,
      conditionalDecodeCircuit, conditionalDecodeElaborated, conditionalDecodeMain,
      readFromMemory, FemtoCairo.decodeInstruction]

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
        have := congrArg State.pc h_input_preState
        simp only [circuit_norm] at this
        exact this
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

        -- Show Expression.eval of rawInstrType equals rawInstr.rawInstrType
        have h_rawInstrType_eval : Expression.eval env (varFromOffset RawInstruction i₀).rawInstrType = rawInstr.rawInstrType := by
          have := congrArg RawInstruction.rawInstrType h_fetch
          simp only [varFromOffset, circuit_norm] at this ⊢
          exact this

        rw [h_rawInstrType_eval] at h_decode_cond

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
            · simp only [DecodedInstructionType.val, h1, zero_ne_one, ↓reduceIte, h2, h3] at h_instr_type
              exact h_instr_type.symm
          simp only [h_isLoadState_eq, ite_true]

          -- Use soundness of memory reads
          specialize h_read1 h_mode1_encoded
          specialize h_read2 h_mode2_encoded
          specialize h_read3 h_mode3_encoded

          -- Rewrite Expression.eval of op fields to actual op values
          have h_op1_eval : Expression.eval env (varFromOffset RawInstruction i₀).op1 = rawInstr.op1 := by
            have := congrArg RawInstruction.op1 h_fetch
            simp only [varFromOffset, circuit_norm] at this ⊢
            exact this
          have h_op2_eval : Expression.eval env (varFromOffset RawInstruction i₀).op2 = rawInstr.op2 := by
            have := congrArg RawInstruction.op2 h_fetch
            simp only [varFromOffset, circuit_norm] at this ⊢
            exact this
          have h_op3_eval : Expression.eval env (varFromOffset RawInstruction i₀).op3 = rawInstr.op3 := by
            have := congrArg RawInstruction.op3 h_fetch
            simp only [varFromOffset, circuit_norm] at this ⊢
            exact this

          rw [h_op1_eval, h_mode1] at h_read1
          rw [h_op2_eval, h_mode2] at h_read2
          rw [h_op3_eval, h_mode3] at h_read3

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
  (LoadStateInstruction.circuit program h_programSize memory h_memorySize) input

instance stepBody_constantLength
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → (F p)) (h_programSize : programSize < p)
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → (F p)) (h_memorySize : memorySize < p) :
    Circuit.ConstantLength (stepBody program h_programSize memory h_memorySize) where
  localLength := 27
  localLength_eq _ _ := by
    simp only [stepBody, circuit_norm]
    rfl

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
    -- Unfold stepBody to assertionChangingMultiset which produces a subcircuit
    simp only [stepBody, assertionChangingMultiset, Circuit.ConstantLength.localLength, circuit_norm]
    -- collectAdds on [.subcircuit s] = s.localAdds
    -- s.localAdds = circuit.localAdds by FormalAssertionChangingMultiset.toSubcircuit_localAdds
    -- circuit.localAdds = elaborated.localAdds by definition
    simp only [LoadStateInstruction.circuit, LoadStateInstruction.elaborated, circuit_norm]
    rfl
  subcircuitsConsistent := by
    intros inputs offset
    rw [Operations.SubcircuitsConsistent, main, Circuit.forEach.forAll]
    intro i
    simp only [stepBody, assertionChangingMultiset, circuit_norm]

/--
Assumptions for the LOAD_STATE bundle.
-/
def Assumptions
    (capacity : ℕ) [NeZero capacity]
    {programSize : ℕ} [NeZero programSize]
    (inputs : ProvableVector InstructionStepInput capacity (F p)) : Prop :=
  ∀ i : Fin capacity, LoadStateInstruction.Assumptions (programSize := programSize) inputs[i]

/--
Specification for the LOAD_STATE bundle.
-/
def Spec
    (capacity : ℕ) [NeZero capacity]
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → (F p))
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → (F p))
    (inputs : ProvableVector InstructionStepInput capacity (F p)) (adds : InteractionDelta (F p)) : Prop :=
  ∃ (stepAdds : Fin capacity → InteractionDelta (F p)),
    (∀ i : Fin capacity, LoadStateInstruction.Spec program memory inputs[i] (stepAdds i)) ∧
    adds = (List.finRange capacity).foldl (fun acc i => acc + stepAdds i) 0

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
    -- Define stepAdds using the circuit's localAdds
    let stepCircuit := LoadStateInstruction.circuit program h_programSize memory h_memorySize
    use fun i => stepCircuit.localAdds inputs_var[i] env (offset + i * 27)
    constructor
    · -- Each step satisfies LoadStateInstruction.Spec
      intro i
      have h_step := h_holds i
      simp only [stepBody, assertionChangingMultiset, circuit_norm] at h_step
      have h_eval_i : eval env inputs_var[i] = inputs[i] :=
        eval_vector_eq_get env inputs_var inputs h_eval i i.isLt
      simp only [show (LoadStateInstruction.circuit program h_programSize memory h_memorySize).Assumptions =
        LoadStateInstruction.Assumptions from rfl,
        show (LoadStateInstruction.circuit program h_programSize memory h_memorySize).Spec =
        LoadStateInstruction.Spec program memory from rfl] at h_step
      have h_record : { enabled := Expression.eval env (Vector.get inputs_var ⟨↑i, i.isLt⟩).enabled,
                        preState := eval env (Vector.get inputs_var ⟨↑i, i.isLt⟩).preState :
                        InstructionStepInput (F p) } = eval env inputs_var[i] := by
        simp only [eval, toVars, toElements, fromElements, circuit_norm]
      rw [h_record, h_eval_i] at h_step
      have h_assump : LoadStateInstruction.Assumptions inputs[i] := h_assumptions i
      convert h_step h_assump using 2
    · -- The adds sum correctly
      simp only [elaborated]
      apply List.foldl_ext
      intro acc i _
      simp only [stepCircuit, LoadStateInstruction.circuit, circuit_norm]
      simp only [Fin.eta, mul_neg, mul_one, List.append_cancel_left_eq]
      -- Unfold ElaboratedCircuit.localAdds for LoadStateInstruction.elaborated
      simp only [LoadStateInstruction.elaborated, circuit_norm]
      -- Now LHS has Vector.get inputs_var i and -enabled
      -- RHS has inputs_var[↑i] and enabled * -1 / enabled * 1
      -- Vector.get v i = v[i] by definition (Fin index)
      simp only [Vector.get_eq_getElem]
      -- Now just need -x = x * -1 and x = x * 1
      ring_nf
  -- Completeness is out of scope for the current work.
  completeness := by sorry

end Bundle

end Examples.PicoCairoMultiplicity.LoadStateInstruction
