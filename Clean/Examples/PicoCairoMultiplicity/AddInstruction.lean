/-
PicoCairoMultiplicity ADD Instruction Circuit
Following PR 286 PicoCairo pattern but using multiplicities instead of timestamps.
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

namespace Examples.PicoCairoMultiplicity.AddInstruction

open Examples.FemtoCairo
open Examples.FemtoCairo.Types
open Examples.FemtoCairo.Spec
open Examples.PicoCairoMultiplicity.Types
open Examples.PicoCairoMultiplicity.Helpers
open Operations (collectAdds collectAdds_flatten collectAdds_ofFn_flatten)
open Circuit (collectAdds_forEach_foldl)

variable {p : ℕ} [Fact p.Prime] [p_large_enough: Fact (p > 512)]

/--
Main circuit for ADD instruction step.
Takes enabled flag and pre-state.
If enabled, executes the ADD instruction and emits multiplicity operations.
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

  -- Step 4: Conditionally decode the instruction (returns dummy ADD when disabled)
  let decoded ← subcircuitWithAssertion conditionalDecodeCircuit {
    enabled := enabled,
    rawInstrType := rawInstruction.rawInstrType,
    dummy := dummyADDInstruction
  }

  -- Step 5: Unconditionally assert it's an ADD instruction
  -- When enabled=1, this checks the actual instruction is ADD
  -- When enabled=0, this always passes since dummy is ADD
  assertZero (decoded.instrType.isAdd - 1)

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

  -- Step 7: Conditional ADD constraint: v3 = v1 + v2 (only when enabled)
  assertZero (enabled * (v3 - (v1 + v2)))

  -- Step 8: Compute next state (pc increments by 4, ap and fp unchanged for ADD)
  let postState : Var State (F p) := {
    pc := preState.pc + 4,
    ap := preState.ap,
    fp := preState.fp
  }

  -- Step 9: Conditionally emit +1 for post-state (producing)
  emitStateWhen enabled 1 postState

/--
Computes the localAdds for a single ADD instruction step.
If enabled, emits pre-state with -1 and post-state with +1.
-/
def localAdds
    (input : InstructionStepInput (F p)) : List (NamedList (F p) × F p) :=
  let preState := input.preState
  let postState : State (F p) := {
    pc := preState.pc + 4,
    ap := preState.ap,
    fp := preState.fp
  }
  [(⟨"state", [preState.pc, preState.ap, preState.fp]⟩, input.enabled * (-1)),
   (⟨"state", [postState.pc, postState.ap, postState.fp]⟩, input.enabled * 1)]

/--
ElaboratedCircuit for ADD instruction step.
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
    simp only [main, circuit_norm, emitStateWhen, emitAdd, FemtoCairo.fetchInstruction,
      conditionalDecodeCircuit, conditionalDecodeElaborated, conditionalDecodeMain,
      readFromMemory, assertBool, FormalAssertion.toSubcircuit, Operations.collectAdds,
      List.nil_append, NamedList.eval, add_zero]
    rfl

/--
Assumptions for the ADD instruction step.
-/
def Assumptions
    {programSize : ℕ} [NeZero programSize]
    (input : InstructionStepInput (F p)) : Prop :=
  IsBool input.enabled ∧
  ZMod.val input.preState.pc + 3 < programSize

/--
Specification for the ADD instruction step.
If enabled, the pre-state consumed and post-state produced must reflect a valid ADD execution.
-/
def Spec
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → (F p))
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → (F p))
    (input : InstructionStepInput (F p)) (adds : InteractionDelta (F p)) : Prop :=
  if input.enabled = 1 then
    -- When enabled, we need to verify:
    -- 1. The pre-state is consumed (multiplicity -1)
    -- 2. The post-state is produced (multiplicity +1)
    -- 3. The ADD operation is valid according to FemtoCairo spec
    match Spec.fetchInstruction program input.preState.pc with
    | some rawInstr =>
      match Spec.decodeInstruction rawInstr.rawInstrType with
      | some (instrType, mode1, mode2, mode3) =>
        if instrType = 0 then  -- Must be ADD
          match Spec.dataMemoryAccess memory rawInstr.op1 mode1 input.preState.ap input.preState.fp,
                Spec.dataMemoryAccess memory rawInstr.op2 mode2 input.preState.ap input.preState.fp,
                Spec.dataMemoryAccess memory rawInstr.op3 mode3 input.preState.ap input.preState.fp with
          | some v1, some v2, some v3 =>
            v1 + v2 = v3 ∧
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
FormalAssertionChangingMultiset for the ADD instruction step.
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
    obtain ⟨_, h_fetch, h_decode_cond, h_isAdd, h_read1, h_read2, h_read3, h_add_constraint⟩ := h_holds

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

        -- h_fetch gives us: eval env (varFromOffset RawInstruction i₀) = rawInstr
        -- We need to extract the rawInstrType field for the decode condition
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

          -- Show instrType = 0 from h_isAdd constraint
          have h_isAdd_eq : instr_type = 0 := by
            -- From h_isAdd: isAdd + -1 = 0, get isAdd = 1
            have h_isAdd_1 := add_neg_eq_zero.mp h_isAdd
            -- Normalize both h_isAdd_1 and h_instr_type to same form, then simplify
            simp only [circuit_norm, explicit_provable_type] at h_isAdd_1 h_instr_type
            simp only [DecodedInstructionType.val, h_isAdd_1, ↓reduceIte] at h_instr_type
            exact h_instr_type.symm
          simp only [h_isAdd_eq, ite_true]

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
            -- v1 + v2 = v3 from ADD constraint
            simp only [h_one, one_mul] at h_add_constraint
            -- Get values from h_read hypotheses
            split at h_read1
            case h_1 val1 h_read1_val =>
              split at h_read2
              case h_1 val2 h_read2_val =>
                split at h_read3
                case h_1 val3 h_read3_val =>
                  -- Now we have h_v1_eq, h_v2_eq, h_v3_eq as well as h_read1_val, h_read2_val, h_read3_val
                  -- both saying dataMemoryAccess = some value
                  have hv1 : v1 = val1 := by simp_all
                  have hv2 : v2 = val2 := by simp_all
                  have hv3 : v3 = val3 := by simp_all
                  rw [hv1, hv2, hv3, ←h_read1, ←h_read2, ←h_read3]
                  -- h_add_constraint: v3 + -(v1 + v2) = 0 means v3 = v1 + v2
                  -- Goal: v1 + v2 = v3
                  have h := h_add_constraint
                  have h' : env.get (i₀ + 4 + 8 + 5 + 5 + 1 + 1 + 1 + 1) =
                            env.get (i₀ + 4 + 8 + 1 + 1 + 1 + 1) + env.get (i₀ + 4 + 8 + 5 + 1 + 1 + 1 + 1) := by
                    have : env.get (i₀ + 4 + 8 + 5 + 5 + 1 + 1 + 1 + 1) +
                           -(env.get (i₀ + 4 + 8 + 1 + 1 + 1 + 1) + env.get (i₀ + 4 + 8 + 5 + 1 + 1 + 1 + 1)) = 0 := h
                    -- From a + -b = 0, we get a = b
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
Bundle of ADD instruction step circuits.
Takes a vector of inputs with given capacity and executes ADD instructions for each enabled input.
-/
def stepBody
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → (F p)) (h_programSize : programSize < p)
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → (F p)) (h_memorySize : memorySize < p)
    (input : Var InstructionStepInput (F p)) : Circuit (F p) Unit :=
  (AddInstruction.circuit program h_programSize memory h_memorySize) input

instance stepBody_constantLength
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → (F p)) (h_programSize : programSize < p)
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → (F p)) (h_memorySize : memorySize < p) :
    Circuit.ConstantLength (stepBody program h_programSize memory h_memorySize) where
  localLength := 27
  localLength_eq _ _ := by
    simp only [stepBody, circuit_norm]
    rfl

def main
    (capacity : ℕ) [NeZero capacity]
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → (F p)) (h_programSize : programSize < p)
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → (F p)) (h_memorySize : memorySize < p)
    (inputs : Var (ProvableVector InstructionStepInput capacity) (F p)) : Circuit (F p) Unit :=
  Circuit.forEach inputs (stepBody program h_programSize memory h_memorySize)
    (stepBody_constantLength program h_programSize memory h_memorySize)

/--
Elaborated circuit for ADD instruction bundle.
-/
def elaborated
    (capacity : ℕ) [NeZero capacity]
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → (F p)) (h_programSize : programSize < p)
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → (F p)) (h_memorySize : memorySize < p) :
    ElaboratedCircuit (F p) (ProvableVector InstructionStepInput capacity) unit where
  main := main capacity program h_programSize memory h_memorySize
  localLength _ := capacity * 27  -- Each step uses 27 locals
  localLength_eq := by
    intros input offset
    simp only [main, Circuit.forEach.localLength_eq]
    congr 1
  output _ _ := ()
  localAdds inputs env offset :=
    -- Sum up localAdds from each instruction step using list fold
    (List.finRange capacity).foldl (fun acc i =>
      let input := eval env inputs[i]
      let preState := input.preState
      let postState : State (F p) := {
        pc := preState.pc + 4,
        ap := preState.ap,
        fp := preState.fp
      }
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
    -- Unfold stepBody and show the localAdds match
    simp only [stepBody, assertionChangingMultiset, Circuit.ConstantLength.localLength]
    -- Use the fact that collectAdds on subcircuit gives localAdds
    simp only [Operations.collectAdds, circuit_norm]
    -- Now we need to show the elaborated circuit's localAdds matches our manual computation
    simp only [AddInstruction.circuit, AddInstruction.elaborated, circuit_norm]
    rfl
  subcircuitsConsistent := by
    intros inputs offset
    rw [Operations.SubcircuitsConsistent, main, Circuit.forEach.forAll]
    intro i
    simp only [stepBody, assertionChangingMultiset, circuit_norm]

/--
Assumptions for the bundle: each input must satisfy the individual step assumptions.
-/
def Assumptions
    (capacity : ℕ) [NeZero capacity]
    {programSize : ℕ} [NeZero programSize]
    (inputs : ProvableVector InstructionStepInput capacity (F p)) : Prop :=
  ∀ i : Fin capacity, AddInstruction.Assumptions (programSize := programSize) inputs[i]

/--
Spec for the bundle: each element satisfies its step spec, and local adds are summed.
-/
def Spec
    (capacity : ℕ) [NeZero capacity]
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → (F p))
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → (F p))
    (inputs : ProvableVector InstructionStepInput capacity (F p))
    (adds : InteractionDelta (F p)) : Prop :=
  ∃ (stepAdds : Fin capacity → InteractionDelta (F p)),
    (∀ i : Fin capacity, AddInstruction.Spec program memory inputs[i] (stepAdds i)) ∧
    adds = (List.finRange capacity).foldl (fun acc i => acc + stepAdds i) 0

/--
FormalAssertionChangingMultiset for ADD instruction bundle.
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
    let stepCircuit := AddInstruction.circuit program h_programSize memory h_memorySize
    use fun i => stepCircuit.localAdds inputs_var[i] env (offset + i * 27)
    constructor
    · -- Each step satisfies AddInstruction.Spec
      intro i
      -- Get constraints for step i
      have h_step := h_holds i
      simp only [stepBody, assertionChangingMultiset, circuit_norm] at h_step
      -- h_step : Assumptions {...} → Spec {...} (localAdds ...)
      -- The record {...} is definitionally equal to eval env inputs_var[i]
      -- We have h_eval : eval env inputs_var = inputs, so (eval env inputs_var)[i] = inputs[i]
      -- And eval env inputs_var[i] = (eval env inputs_var)[i] by eval_vector_eq_get
      have h_eval_i : eval env inputs_var[i] = inputs[i] :=
        eval_vector_eq_get env inputs_var inputs h_eval i i.isLt
      -- The assumption and spec in h_step match when we substitute
      -- The record { enabled := ..., preState := ... } expands from eval, use simp to normalize
      simp only [show (AddInstruction.circuit program h_programSize memory h_memorySize).Assumptions =
        AddInstruction.Assumptions from rfl,
        show (AddInstruction.circuit program h_programSize memory h_memorySize).Spec =
        AddInstruction.Spec program memory from rfl] at h_step
      -- The record in h_step is equal to eval env inputs_var[i], which equals inputs[i] by h_eval_i
      -- First show the record equals eval env inputs_var[i]
      have h_record : { enabled := Expression.eval env (Vector.get inputs_var ⟨↑i, i.isLt⟩).enabled,
                        preState := eval env (Vector.get inputs_var ⟨↑i, i.isLt⟩).preState :
                        InstructionStepInput (F p) } = eval env inputs_var[i] := by
        simp only [eval, toVars, toElements, fromElements, circuit_norm]
      rw [h_record, h_eval_i] at h_step
      -- Now h_step gives us inputs[i] → Spec for inputs[i]
      -- The difference between inputs_var[↑i] and inputs_var[i] is just the coercion (defeq)
      -- Also localLength unit default = 27
      -- Apply with assumptions
      -- h_assumptions : Assumptions capacity inputs = ∀ j, AddInstruction.Assumptions inputs[j]
      have h_assump : AddInstruction.Assumptions inputs[i] := h_assumptions i
      convert h_step h_assump using 2
    · -- The adds sum correctly
      simp only [elaborated]
      apply List.foldl_ext
      intro acc i _
      simp only [stepCircuit, AddInstruction.circuit, circuit_norm]
      simp only [Fin.eta, mul_neg, mul_one, List.append_cancel_left_eq]
      -- Unfold ElaboratedCircuit.localAdds for AddInstruction.elaborated
      simp only [AddInstruction.elaborated, circuit_norm]
      -- Now LHS has Vector.get inputs_var i and -enabled
      -- RHS has inputs_var[↑i] and enabled * -1 / enabled * 1
      -- Vector.get v i = v[i] by definition (Fin index)
      simp only [Vector.get_eq_getElem]
      -- Now just need -x = x * -1 and x = x * 1
      ring_nf

  -- Completeness is out of scope for the current work.
  -- The proof would require showing that if Spec holds for some stepAdds (from the existential
  -- in Bundle.Spec), then the circuit's actual localAdds also satisfies it. Since
  -- AddInstruction.Spec is deterministic in adds, these must coincide when assumptions hold.
  completeness := by sorry

end Bundle

end Examples.PicoCairoMultiplicity.AddInstruction
