import Clean.Gadgets.BLAKE3.BLAKE3State
import Clean.Gadgets.BLAKE3.Round
import Clean.Gadgets.BLAKE3.Permute
import Clean.Types.U32
import Clean.Circuit.Provable
import Clean.Specs.BLAKE3
import Clean.Circuit.StructuralLemmas

namespace Gadgets.BLAKE3.ApplyRounds
variable {p : ℕ} [Fact p.Prime] [p_large_enough: Fact (p > 2^16 + 2^8)]
instance : Fact (p > 512) := .mk (by linarith [p_large_enough.elim])

open Specs.BLAKE3 (applyRounds iv round permute)

/--
Lemma to handle the notational difference between BLAKE3State.value and Vector.map U32.value.
-/
lemma blake3_value_eq_map_value {p : ℕ} (msg : Vector (U32 (F p)) 16) :
  BLAKE3State.value msg = Vector.map U32.value msg := rfl

/--
A FormalCircuit that performs one round followed by permuting the message.
Both input and output are Round.Inputs (state and message).

The spec follows the pattern from the applyRounds function:
- Apply round to get new state
- Permute the message
-/
def roundWithPermute : FormalCircuit (F p) Round.Inputs Round.Inputs := {
  elaborated := {
    main := fun input => do
      let state ← subcircuit Round.circuit input
      let permuted_message ← subcircuit Permute.circuit input.message
      return ⟨state, permuted_message⟩
    localLength := fun _ => Round.circuit.localLength _ + Permute.circuit.localLength _
    localLength_eq := by
      intro input offset
      simp only [Circuit.bind_def, Circuit.localLength, circuit_norm]
      rfl
    output := fun input offset =>
      let state_out := Round.circuit.output input offset
      let msg_out := Permute.circuit.output input.message (offset + Round.circuit.localLength input)
      ⟨state_out, msg_out⟩
    output_eq := by
      intro input offset
      simp only [Circuit.bind_def, Circuit.output, circuit_norm]
    subcircuitsConsistent := by
      intro input offset
      simp only [Circuit.bind_def, Circuit.operations, circuit_norm]
      have h : offset + Round.circuit.localLength input = Round.circuit.localLength input + offset := by ring
      rw [h]
  }
  Assumptions := Round.Assumptions
  Spec := fun input output =>
    let state' := round input.state.value (BLAKE3State.value input.message)
    output.state.value = state' ∧
    output.state.Normalized ∧
    BLAKE3State.value output.message = permute (BLAKE3State.value input.message) ∧
    BLAKE3State.Normalized output.message
  soundness := by
    intro offset env input_var input h_eval h_assumptions h_holds
    simp only [circuit_norm, subcircuit_norm] at h_holds
    rcases h_holds with ⟨ h_holds1, h_holds2 ⟩
    simp only [Round.circuit] at h_holds1
    rcases input with ⟨ input_state, input_msg ⟩
    have h1 : Round.Inputs.mk (eval env input_var.state) (eval env input_var.message : ProvableVector U32 16 (F p)) = eval env input_var := by
      rw [ProvableStruct.eval_eq_eval]
      simp only [ProvableStruct.eval]
      rfl
    rw [h_eval] at h1
    simp only [h1] at h_holds1 h_holds2
    specialize h_holds1 h_assumptions
    simp only [Permute.circuit, Permute.Assumptions] at h_holds2
    rcases h_assumptions with ⟨ asm1, asm2 ⟩

    have asm2' : (eval env input_var.message : BLAKE3State _).Normalized := by
      have h_msg_eq : (eval env input_var.message : BLAKE3State _) = input_msg := by
        injection h1
      rw [h_msg_eq]
      exact asm2

    -- h_holds2 requires the message to be normalized
    specialize h_holds2 asm2'

    -- Now we need to show the spec holds for the output
    intro output

    have h_output_struct : output = {
      state := eval env (Round.circuit.output input_var offset),
      message := eval env (Permute.circuit.output input_var.message (offset + Round.circuit.localLength input_var))
    } := by
      unfold output
      simp only [roundWithPermute.output_eq]
      rw [ProvableStruct.eval_eq_eval]
      simp only [ProvableStruct.eval]
      rfl

    constructor
    · rw [h_output_struct]
      simp only [Round.Spec] at h_holds1
      exact h_holds1.1
    constructor
    · rw [h_output_struct]
      simp only [Round.Spec] at h_holds1
      exact h_holds1.2
    constructor
    · rw [h_output_struct]
      simp only [Permute.Spec] at h_holds2
      have h_msg_eq : (eval env input_var.message : BLAKE3State _) = input_msg := by
        injection h1
      rw [h_msg_eq] at h_holds2
      exact h_holds2.1
    · rw [h_output_struct]
      simp only [Permute.Spec] at h_holds2
      have h_msg_eq : (eval env input_var.message : BLAKE3State _) = input_msg := by
        injection h1
      rw [h_msg_eq] at h_holds2
      exact h_holds2.2

  completeness := by
    intro offset env input_var h_env_uses_witnesses input h_eval h_assumptions

    rcases input with ⟨ input_state, input_msg ⟩
    have h1 : Round.Inputs.mk (eval env input_var.state) (eval env input_var.message : ProvableVector U32 16 (F p)) = eval env input_var := by
      rw [ProvableStruct.eval_eq_eval]
      simp only [ProvableStruct.eval]
      rfl

    -- Unpack what we have
    simp only [circuit_norm, subcircuit_norm] at h_env_uses_witnesses ⊢
    obtain ⟨h_round_uses, h_permute_uses⟩ := h_env_uses_witnesses

    constructor
    · rw [← h_eval] at h_assumptions
      rw [h1]
      exact h_assumptions

    · -- Show Permute assumptions hold (message is normalized)
      rcases h_assumptions with ⟨_, h_msg_norm⟩
      -- Now h_state_eq : eval env input_var.state = input_state
      -- and h_msg_eq : (eval env input_var.message : ProvableVector U32 16 (F p)) = input_msg

      dsimp only [Permute.circuit, Permute.Assumptions]
      -- We need to show (eval env input_var.message).Normalized
      -- We know from h_eval that eval env input_var = { state := input_state, message := input_msg }
      -- So eval env input_var.message = input_msg
      -- We need to show that eval env input_var.message = input_msg
      -- From h1 and h_eval we can derive this
      have h_eq : Round.Inputs.mk (eval env input_var.state) (eval env input_var.message : ProvableVector U32 16 (F p)) =
                  Round.Inputs.mk input_state input_msg := by
        calc Round.Inputs.mk (eval env input_var.state) (eval env input_var.message : ProvableVector U32 16 (F p))
          _ = eval env input_var := h1
          _ = Round.Inputs.mk input_state input_msg := h_eval

      -- Extract the message equality
      have h_msg_eq : (eval env input_var.message : ProvableVector U32 16 (F p)) = input_msg := by
        injection h_eq

      -- Now we need to cast this to the right type for Normalized
      have h_cast : (eval env input_var.message : BLAKE3State (F p)) = input_msg := by
        exact h_msg_eq

      -- Now we can rewrite and apply h_msg_norm
      rw [h_cast]
      exact h_msg_norm
}

/--
Combines two roundWithPermute operations using the concat combinator.
This performs two rounds with message permutation between them.
-/
def twoRoundsWithPermute : FormalCircuit (F p) Round.Inputs Round.Inputs :=
  roundWithPermute.concat roundWithPermute (by
    -- Prove compatibility: for all inputs, if circuit1 assumptions and spec hold,
    -- then circuit2 assumptions hold
    intro input mid h_asm h_spec
    -- roundWithPermute.Spec gives us that mid.state.Normalized and message is normalized
    -- We need to show Round.Assumptions mid
    simp only [roundWithPermute] at h_spec ⊢
    constructor
    · -- mid.state.Normalized
      exact h_spec.2.1
    · -- ∀ i : Fin 16, mid.message[i].Normalized
      exact h_spec.2.2.2
  ) (by
    -- Prove h_localLength_stable: roundWithPermute.localLength doesn't depend on input
    intro mid mid'
    -- roundWithPermute.localLength is defined as fun _ => constant
    -- So it's the same for any input
    rfl
  )

/--
Apply two rounds of BLAKE3 compression, starting from a Round.Inputs state.
This follows the same pattern as applyRounds but for only 2 rounds:
- First round, permute message
- Second round, permute message
Returns the final state and permuted message.
-/
def applyTwoRounds (state : Vector Nat 16) (message : Vector Nat 16) : Vector Nat 16 × Vector Nat 16 :=
  let state1 := round state message
  let msg1 := permute message
  let state2 := round state1 msg1
  let msg2 := permute msg1
  (state2, msg2)

/--
Specification for two rounds that matches the pattern of the full ApplyRounds.Spec.
-/
def TwoRoundsSpec (input : Round.Inputs (F p)) (output : Round.Inputs (F p)) : Prop :=
  let (final_state, final_message) := applyTwoRounds input.state.value (input.message.map U32.value)
  output.state.value = final_state ∧
  output.message.map U32.value = final_message ∧
  output.state.Normalized ∧
  (∀ i : Fin 16, output.message[i].Normalized)


/--
Two rounds with permute, but with a spec matching the applyRounds pattern.
-/
def twoRoundsApplyStyle : FormalCircuit (F p) Round.Inputs Round.Inputs :=
  twoRoundsWithPermute.weakenSpec TwoRoundsSpec (by
    -- Prove that twoRoundsWithPermute's spec implies our TwoRoundsSpec
    intro input output h_assumptions h_spec
    -- twoRoundsWithPermute.Spec says ∃ mid, roundWithPermute.Spec input mid ∧ roundWithPermute.Spec mid output
    obtain ⟨mid, h_spec1, h_spec2⟩ := h_spec
    -- Unpack what each roundWithPermute spec gives us
    simp only [roundWithPermute] at h_spec1 h_spec2
    simp only [TwoRoundsSpec, applyTwoRounds]

    -- From h_spec1: mid.state.value = round input.state.value (BLAKE3State.value input.message)
    -- From h_spec1: BLAKE3State.value mid.message = permute (BLAKE3State.value input.message)
    -- From h_spec2: output.state.value = round mid.state.value (BLAKE3State.value mid.message)
    -- From h_spec2: BLAKE3State.value output.message = permute (BLAKE3State.value mid.message)

    constructor
    · -- Prove: output.state.value = round (round input.state.value (input.message.map U32.value)) (permute (input.message.map U32.value))
      rw [h_spec2.1, h_spec1.1]
      -- Need to show BLAKE3State.value mid.message = permute (Vector.map U32.value input.message)
      -- We have h_spec1.2.2.1: BLAKE3State.value mid.message = permute (BLAKE3State.value input.message)
      -- Need to show BLAKE3State.value input.message = Vector.map U32.value input.message
      rw [h_spec1.2.2.1]
      -- Show BLAKE3State.value input.message = Vector.map U32.value input.message
      rfl
    constructor
    · -- Prove: output.message.map U32.value = permute (permute (input.message.map U32.value))
      -- We have h_spec2.2.2.1: BLAKE3State.value output.message = permute (BLAKE3State.value mid.message)
      -- We have h_spec1.2.2.1: BLAKE3State.value mid.message = permute (BLAKE3State.value input.message)
      -- Use our lemma to convert between the notations
      rw [← blake3_value_eq_map_value output.message]
      rw [h_spec2.2.2.1, h_spec1.2.2.1]
      rw [blake3_value_eq_map_value input.message]
    constructor
    · -- Prove: output.state.Normalized
      exact h_spec2.2.1
    · -- Prove: ∀ i : Fin 16, output.message[i].Normalized
      exact h_spec2.2.2.2
  )

/--
Combines four rounds with permutation using two twoRoundsWithPermute operations.
This performs four rounds with message permutation between them.
-/
def fourRoundsWithPermute : FormalCircuit (F p) Round.Inputs Round.Inputs :=
  twoRoundsWithPermute.concat twoRoundsWithPermute (by
    -- Prove compatibility: if first twoRoundsWithPermute assumptions and spec hold,
    -- then second twoRoundsWithPermute assumptions hold
    intro input mid h_asm h_spec
    -- twoRoundsWithPermute.Spec says ∃ mid', roundWithPermute.Spec input mid' ∧ roundWithPermute.Spec mid' mid
    obtain ⟨mid', h_spec1, h_spec2⟩ := h_spec
    -- We need to show twoRoundsWithPermute.Assumptions mid
    -- which is the same as roundWithPermute.Assumptions mid, which is Round.Assumptions mid
    simp only [twoRoundsWithPermute, roundWithPermute] at h_spec2 ⊢
    constructor
    · -- mid.state.Normalized
      exact h_spec2.2.1
    · -- ∀ i : Fin 16, mid.message[i].Normalized
      exact h_spec2.2.2.2
  ) (by
    -- Prove h_localLength_stable: twoRoundsWithPermute.localLength doesn't depend on input
    intro mid mid'
    -- twoRoundsWithPermute.localLength is constant
    rfl
  )

/--
Apply four rounds of BLAKE3 compression, starting from a Round.Inputs state.
This follows the same pattern as applyRounds but for only 4 rounds:
- First round, permute message
- Second round, permute message
- Third round, permute message
- Fourth round, permute message
Returns the final state and permuted message.
-/
def applyFourRounds (state : Vector Nat 16) (message : Vector Nat 16) : Vector Nat 16 × Vector Nat 16 :=
  let state1 := round state message
  let msg1 := permute message
  let state2 := round state1 msg1
  let msg2 := permute msg1
  let state3 := round state2 msg2
  let msg3 := permute msg2
  let state4 := round state3 msg3
  let msg4 := permute msg3
  (state4, msg4)

/--
Specification for four rounds that matches the pattern of the full ApplyRounds.Spec.
-/
def FourRoundsSpec (input : Round.Inputs (F p)) (output : Round.Inputs (F p)) : Prop :=
  let (final_state, final_message) := applyFourRounds input.state.value (input.message.map U32.value)
  output.state.value = final_state ∧
  output.message.map U32.value = final_message ∧
  output.state.Normalized ∧
  (∀ i : Fin 16, output.message[i].Normalized)

/--
Four rounds with permute, but with a spec matching the applyRounds pattern.
-/
def fourRoundsApplyStyle : FormalCircuit (F p) Round.Inputs Round.Inputs :=
  fourRoundsWithPermute.weakenSpec FourRoundsSpec (by
    -- Prove that fourRoundsWithPermute's spec implies our FourRoundsSpec
    intro input output h_assumptions h_spec
    -- fourRoundsWithPermute.Spec says ∃ mid, twoRoundsWithPermute.Spec input mid ∧ twoRoundsWithPermute.Spec mid output
    obtain ⟨mid, h_spec1, h_spec2⟩ := h_spec
    -- Each twoRoundsWithPermute.Spec says ∃ mid', roundWithPermute.Spec ... ∧ roundWithPermute.Spec ...
    obtain ⟨mid1, h_spec1_1, h_spec1_2⟩ := h_spec1
    obtain ⟨mid2, h_spec2_1, h_spec2_2⟩ := h_spec2

    simp only [roundWithPermute] at h_spec1_1 h_spec1_2 h_spec2_1 h_spec2_2
    simp only [FourRoundsSpec, applyFourRounds, applyTwoRounds]

    -- Build the result by chaining the four rounds
    constructor
    · -- Prove: output.state.value = final_state after 4 rounds
      rw [h_spec2_2.1, h_spec2_1.1, h_spec1_2.1, h_spec1_1.1]
      -- Use the fact that BLAKE3State.value = Vector.map U32.value
      rw [h_spec2_1.2.2.1, h_spec1_2.2.2.1, h_spec1_1.2.2.1]
      rfl
    constructor
    · -- Prove: output.message.map U32.value = final_message after 4 rounds
      rw [← blake3_value_eq_map_value output.message]
      rw [h_spec2_2.2.2.1, h_spec2_1.2.2.1, h_spec1_2.2.2.1, h_spec1_1.2.2.1]
      rw [blake3_value_eq_map_value input.message]
    constructor
    · -- Prove: output.state.Normalized
      exact h_spec2_2.2.1
    · -- Prove: ∀ i : Fin 16, output.message[i].Normalized
      exact h_spec2_2.2.2.2
  )

/--
Combines six rounds with permutation using fourRoundsWithPermute and twoRoundsWithPermute.
This performs six rounds with message permutation between them.
-/
def sixRoundsWithPermute : FormalCircuit (F p) Round.Inputs Round.Inputs :=
  fourRoundsWithPermute.concat twoRoundsWithPermute (by
    -- Prove compatibility: if fourRoundsWithPermute assumptions and spec hold,
    -- then twoRoundsWithPermute assumptions hold
    intro input mid h_asm h_spec
    -- fourRoundsWithPermute.Spec says ∃ mid', twoRoundsWithPermute.Spec ... ∧ twoRoundsWithPermute.Spec ...
    obtain ⟨mid', h_spec1, h_spec2⟩ := h_spec
    -- Each twoRoundsWithPermute.Spec says ∃ mid'', roundWithPermute.Spec ... ∧ roundWithPermute.Spec ...
    obtain ⟨mid'', h_spec2_1, h_spec2_2⟩ := h_spec2
    -- We need to show twoRoundsWithPermute.Assumptions mid
    -- which is the same as roundWithPermute.Assumptions mid, which is Round.Assumptions mid
    simp only [twoRoundsWithPermute, roundWithPermute] at h_spec2_2 ⊢
    constructor
    · -- mid.state.Normalized
      exact h_spec2_2.2.1
    · -- ∀ i : Fin 16, mid.message[i].Normalized
      exact h_spec2_2.2.2.2
  ) (by
    -- Prove h_localLength_stable: twoRoundsWithPermute.localLength doesn't depend on input
    intro mid mid'
    -- twoRoundsWithPermute.localLength is constant
    rfl
  )

/--
Apply six rounds of BLAKE3 compression, starting from a Round.Inputs state.
This follows the same pattern as applyRounds but for only 6 rounds:
- First through sixth rounds, each followed by permute message
Returns the final state and permuted message.
-/
def applySixRounds (state : Vector Nat 16) (message : Vector Nat 16) : Vector Nat 16 × Vector Nat 16 :=
  let state1 := round state message
  let msg1 := permute message
  let state2 := round state1 msg1
  let msg2 := permute msg1
  let state3 := round state2 msg2
  let msg3 := permute msg2
  let state4 := round state3 msg3
  let msg4 := permute msg3
  let state5 := round state4 msg4
  let msg5 := permute msg4
  let state6 := round state5 msg5
  let msg6 := permute msg5
  (state6, msg6)

/--
Specification for six rounds that matches the pattern of the full ApplyRounds.Spec.
-/
def SixRoundsSpec (input : Round.Inputs (F p)) (output : Round.Inputs (F p)) : Prop :=
  let (final_state, final_message) := applySixRounds input.state.value (input.message.map U32.value)
  output.state.value = final_state ∧
  output.message.map U32.value = final_message ∧
  output.state.Normalized ∧
  (∀ i : Fin 16, output.message[i].Normalized)

/--
Six rounds with permute, but with a spec matching the applyRounds pattern.
-/
def sixRoundsApplyStyle : FormalCircuit (F p) Round.Inputs Round.Inputs :=
  sixRoundsWithPermute.weakenSpec SixRoundsSpec (by
    -- Prove that sixRoundsWithPermute's spec implies our SixRoundsSpec
    intro input output h_assumptions h_spec
    -- sixRoundsWithPermute.Spec says ∃ mid, fourRoundsWithPermute.Spec input mid ∧ twoRoundsWithPermute.Spec mid output
    obtain ⟨mid, h_spec1, h_spec2⟩ := h_spec
    -- Break down fourRoundsWithPermute.Spec
    obtain ⟨mid1, h_spec1_1, h_spec1_2⟩ := h_spec1
    obtain ⟨mid1_1, h_spec1_1_1, h_spec1_1_2⟩ := h_spec1_1
    obtain ⟨mid1_2, h_spec1_2_1, h_spec1_2_2⟩ := h_spec1_2
    -- Break down twoRoundsWithPermute.Spec
    obtain ⟨mid2, h_spec2_1, h_spec2_2⟩ := h_spec2

    simp only [roundWithPermute] at h_spec1_1_1 h_spec1_1_2 h_spec1_2_1 h_spec1_2_2 h_spec2_1 h_spec2_2
    simp only [SixRoundsSpec, applySixRounds]

    -- Build the result by chaining the six rounds
    constructor
    · -- Prove: output.state.value = final_state after 6 rounds
      rw [h_spec2_2.1, h_spec2_1.1, h_spec1_2_2.1, h_spec1_2_1.1, h_spec1_1_2.1, h_spec1_1_1.1]
      -- Use the fact that BLAKE3State.value = Vector.map U32.value
      rw [h_spec2_1.2.2.1, h_spec1_2_2.2.2.1, h_spec1_2_1.2.2.1, h_spec1_1_2.2.2.1, h_spec1_1_1.2.2.1]
      rfl
    constructor
    · -- Prove: output.message.map U32.value = final_message after 6 rounds
      rw [← blake3_value_eq_map_value output.message]
      rw [h_spec2_2.2.2.1, h_spec2_1.2.2.1, h_spec1_2_2.2.2.1, h_spec1_2_1.2.2.1, h_spec1_1_2.2.2.1, h_spec1_1_1.2.2.1]
      rw [blake3_value_eq_map_value input.message]
    constructor
    · -- Prove: output.state.Normalized
      exact h_spec2_2.2.1
    · -- Prove: ∀ i : Fin 16, output.message[i].Normalized
      exact h_spec2_2.2.2.2
  )

/--
Seven rounds with permutation: combines sixRoundsApplyStyle with a final round.
This represents the complete 7-round BLAKE3 compression function.
-/
def sevenRoundsFinal : FormalCircuit (F p) Round.Inputs BLAKE3State :=
  sixRoundsApplyStyle.concat Round.circuit (by
    -- Prove compatibility: sixRoundsApplyStyle output satisfies Round.circuit assumptions
    intro input mid h_asm h_spec
    -- sixRoundsApplyStyle.Spec gives us normalized outputs
    simp only [sixRoundsApplyStyle, FormalCircuit.weakenSpec, SixRoundsSpec] at h_spec
    -- We need to show Round.Assumptions mid
    constructor
    · -- mid.state.Normalized
      exact h_spec.2.2.1
    · -- ∀ i : Fin 16, mid.message[i].Normalized
      exact h_spec.2.2.2
  ) (by
    -- Prove h_localLength_stable: Round.circuit.localLength doesn't depend on input
    intro mid mid'
    -- Round.circuit.localLength is constant
    rfl
  )

/--
Apply seven rounds of BLAKE3 compression, starting from a Round.Inputs state.
This follows the same pattern as applyRounds but for 7 rounds:
- First through sixth rounds, each followed by permute message
- Seventh round (final, no permutation)
Returns the final BLAKE3State.
-/
def applySevenRounds (state : Vector Nat 16) (message : Vector Nat 16) : Vector Nat 16 :=
  let state1 := round state message
  let msg1 := permute message
  let state2 := round state1 msg1
  let msg2 := permute msg1
  let state3 := round state2 msg2
  let msg3 := permute msg2
  let state4 := round state3 msg3
  let msg4 := permute msg3
  let state5 := round state4 msg4
  let msg5 := permute msg4
  let state6 := round state5 msg5
  let msg6 := permute msg5
  let state7 := round state6 msg6
  state7

/--
Specification for seven rounds that matches the pattern of the full ApplyRounds.Spec.
-/
def SevenRoundsSpec (input : Round.Inputs (F p)) (output : BLAKE3State (F p)) : Prop :=
  let final_state := applySevenRounds input.state.value (input.message.map U32.value)
  output.value = final_state ∧
  output.Normalized

/--
Seven rounds with spec matching the applyRounds pattern.
-/
def sevenRoundsApplyStyle : FormalCircuit (F p) Round.Inputs BLAKE3State :=
  sevenRoundsFinal.weakenSpec SevenRoundsSpec (by
    -- Prove that sevenRoundsFinal's spec implies our SevenRoundsSpec
    intro input output h_assumptions h_spec
    -- sevenRoundsFinal.Spec says ∃ mid, sixRoundsApplyStyle.Spec input mid ∧ Round.circuit.Spec mid output
    obtain ⟨mid, h_spec1, h_spec2⟩ := h_spec
    -- Break down the specs similar to previous proofs
    simp only [sixRoundsApplyStyle, FormalCircuit.weakenSpec, SixRoundsSpec] at h_spec1
    simp only [Round.circuit, Round.Spec] at h_spec2
    simp only [SevenRoundsSpec, applySevenRounds, applySixRounds]

    -- Build the result by chaining all seven rounds
    constructor
    · -- Prove: output.value = final_state after 7 rounds
      rw [h_spec2.1, h_spec1.1]
      simp only [applySixRounds]
      congr 1
      rw [h_spec1.2.1]
      simp only [applySixRounds]
    · -- Prove: output.Normalized
      exact h_spec2.2
  )

structure Inputs (F : Type) where
  chaining_value : Vector (U32 F) 8
  block_words : Vector (U32 F) 16
  counter_high : U32 F
  counter_low : U32 F
  block_len : U32 F
  flags : U32 F

instance : ProvableStruct Inputs where
  components := [ProvableVector U32 8, ProvableVector U32 16, U32, U32, U32, U32]
  toComponents := fun { chaining_value, block_words, counter_high, counter_low, block_len, flags } =>
    .cons chaining_value (.cons block_words (.cons counter_high (.cons counter_low (.cons block_len (.cons flags .nil)))))
  fromComponents := fun (.cons chaining_value (.cons block_words (.cons counter_high (.cons counter_low (.cons block_len (.cons flags .nil)))))) =>
    { chaining_value, block_words, counter_high, counter_low, block_len, flags }

def main (input : Var Inputs (F p)) : Circuit (F p) (Var BLAKE3State (F p)) := do
  let { chaining_value, block_words, counter_high, counter_low, block_len, flags } := input

  let state : Var BLAKE3State (F p) := #v[
    chaining_value[0], chaining_value[1], chaining_value[2], chaining_value[3],
    chaining_value[4], chaining_value[5], chaining_value[6], chaining_value[7],
    U32.decomposeNatExpr iv[0], U32.decomposeNatExpr iv[1],
    U32.decomposeNatExpr iv[2], U32.decomposeNatExpr iv[3],
    counter_low, counter_high, block_len, flags
  ]

  -- Apply 7 rounds with message permutation between rounds (except the last)
  let state ← subcircuit sevenRoundsApplyStyle ⟨state, block_words⟩

  return state

-- #eval! main (p:=pBabybear) default |>.localLength
-- #eval! main (p:=pBabybear) default |>.output
instance elaborated : ElaboratedCircuit (F p) Inputs BLAKE3State where
  main := main
  localLength _ := 5376
  localLength_eq input i0 := by
    dsimp only [main, Round.circuit, sevenRoundsApplyStyle, sevenRoundsFinal, sixRoundsApplyStyle, sixRoundsWithPermute,
      fourRoundsWithPermute, twoRoundsWithPermute, roundWithPermute, FormalCircuit.weakenSpec,
      FormalCircuit.concat,
      Permute.circuit, Circuit.pure_def, Circuit.bind_def,
      subcircuit.eq_1, ElaboratedCircuit.output, Circuit.output, FormalCircuit.toSubcircuit.eq_1,
      ElaboratedCircuit.main, Circuit.operations, ElaboratedCircuit.localLength, List.cons_append,
      List.nil_append, ↓Fin.getElem_fin, Operations.localLength.eq_5, Operations.localLength.eq_1,
      Nat.add_zero, Circuit.localLength, Operations.localLength, Nat.reduceAdd]

def Assumptions (input : Inputs (F p)) :=
  let { chaining_value, block_words, counter_high, counter_low, block_len, flags } := input
  (∀ i : Fin 8, chaining_value[i].Normalized) ∧
  (∀ i : Fin 16, block_words[i].Normalized) ∧
  counter_high.Normalized ∧ counter_low.Normalized ∧ block_len.Normalized ∧ flags.Normalized

def Spec (input : Inputs (F p)) (out: BLAKE3State (F p)) :=
  let { chaining_value, block_words, counter_high, counter_low, block_len, flags } := input
  out.value = applyRounds
    (chaining_value.map U32.value)
    (block_words.map U32.value)
    (counter_low.value + 2^32 * counter_high.value)
    block_len.value
    flags.value ∧
  out.Normalized

/--
Lemma showing that applyRounds can be expressed using applySevenRounds.
This connects the spec-level function with our circuit implementation.
-/
lemma applyRounds_eq_applySevenRounds
    (chaining_value : Vector Nat 8)
    (block_words : Vector Nat 16)
    (counter : Nat)
    (block_len : Nat)
    (flags : Nat) :
    applyRounds chaining_value block_words counter block_len flags =
    applySevenRounds
      (#v[
        chaining_value[0], chaining_value[1], chaining_value[2], chaining_value[3],
        chaining_value[4], chaining_value[5], chaining_value[6], chaining_value[7],
        iv[0], iv[1], iv[2], iv[3],
        counter % 2^32, counter / 2^32, block_len, flags
      ])
      block_words := by
  -- applyRounds constructs the same initial state and then applies 7 rounds
  simp only [applyRounds, applySevenRounds]

/--
Lemma showing that evaluating U32.decomposeNatExpr of iv[0] gives iv[0].
-/
lemma eval_decomposeNatExpr_iv_0 (env : Environment (F p)) :
    (eval env (U32.decomposeNatExpr iv[0])).value = iv[0] := by
  simp only [U32.decomposeNatExpr, U32.decomposeNat, eval, toVars, fromElements, toElements]
  simp only [Vector.map, Vector.getElem_mk, Expression.eval, U32.value, U32.vals]
  simp only [iv, Vector.getElem_mk]
  simp only [List.getElem_toArray, List.getElem_cons_zero, Nat.reduceMod, Nat.cast_ofNat,
    Nat.reduceDiv, Nat.reducePow, List.map_toArray, List.map_cons, List.map_nil]
  simp only [Expression.eval]
  -- All these values are less than p, so ZMod.val gives back the original value
  have h1 : ZMod.val (103 : F p) = 103 := ZMod.val_cast_of_lt (by linarith [p_large_enough.elim] : 103 < p)
  have h2 : ZMod.val (230 : F p) = 230 := ZMod.val_cast_of_lt (by linarith [p_large_enough.elim] : 230 < p)
  have h3 : ZMod.val (9 : F p) = 9 := ZMod.val_cast_of_lt (by linarith [p_large_enough.elim] : 9 < p)
  have h4 : ZMod.val (106 : F p) = 106 := ZMod.val_cast_of_lt (by linarith [p_large_enough.elim] : 106 < p)
  rw [h1, h2, h3, h4]

/--
Lemma showing that evaluating U32.decomposeNatExpr of iv[1] gives iv[1].
-/
lemma eval_decomposeNatExpr_iv_1 (env : Environment (F p)) :
    (eval env (U32.decomposeNatExpr iv[1])).value = iv[1] := by
  simp only [U32.decomposeNatExpr, U32.decomposeNat, eval, toVars, fromElements, toElements]
  simp only [Vector.map, Vector.getElem_mk, Expression.eval, U32.value, U32.vals]
  simp only [iv, Vector.getElem_mk]
  simp only [List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ,
    Nat.reduceMod, Nat.cast_ofNat, Nat.reduceDiv, Nat.reducePow, List.map_toArray, List.map_cons, List.map_nil]
  simp only [Expression.eval]
  -- All these values are less than p, so ZMod.val gives back the original value
  have h1 : ZMod.val (133 : F p) = 133 := ZMod.val_cast_of_lt (by linarith [p_large_enough.elim] : 133 < p)
  have h2 : ZMod.val (174 : F p) = 174 := ZMod.val_cast_of_lt (by linarith [p_large_enough.elim] : 174 < p)
  have h3 : ZMod.val (103 : F p) = 103 := ZMod.val_cast_of_lt (by linarith [p_large_enough.elim] : 103 < p)
  have h4 : ZMod.val (187 : F p) = 187 := ZMod.val_cast_of_lt (by linarith [p_large_enough.elim] : 187 < p)
  rw [h1, h2, h3, h4]

/--
Lemma showing that evaluating U32.decomposeNatExpr of iv[2] gives iv[2].
-/
lemma eval_decomposeNatExpr_iv_2 (env : Environment (F p)) :
    (eval env (U32.decomposeNatExpr iv[2])).value = iv[2] := by
  simp only [U32.decomposeNatExpr, U32.decomposeNat, eval, toVars, fromElements, toElements]
  simp only [Vector.map, Vector.getElem_mk, Expression.eval, U32.value, U32.vals]
  simp only [iv, Vector.getElem_mk]
  simp only [List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ,
    Nat.reduceMod, Nat.cast_ofNat, Nat.reduceDiv, Nat.reducePow, List.map_toArray, List.map_cons, List.map_nil]
  simp only [Expression.eval]
  -- All these values are less than p, so ZMod.val gives back the original value
  have h1 : ZMod.val (114 : F p) = 114 := ZMod.val_cast_of_lt (by linarith [p_large_enough.elim] : 114 < p)
  have h2 : ZMod.val (243 : F p) = 243 := ZMod.val_cast_of_lt (by linarith [p_large_enough.elim] : 243 < p)
  have h3 : ZMod.val (60 : F p) = 60 := ZMod.val_cast_of_lt (by linarith [p_large_enough.elim] : 60 < p)
  have h4 : ZMod.val (110 : F p) = 110 := ZMod.val_cast_of_lt (by linarith [p_large_enough.elim] : _ < p)
  rw [h1, h2, h3, h4]

/--
Lemma showing that evaluating U32.decomposeNatExpr of iv[3] gives iv[3].
-/
lemma eval_decomposeNatExpr_iv_3 (env : Environment (F p)) :
    (eval env (U32.decomposeNatExpr iv[3])).value = iv[3] := by
  simp only [U32.decomposeNatExpr, U32.decomposeNat, eval, toVars, fromElements, toElements]
  simp only [Vector.map, Vector.getElem_mk, Expression.eval, U32.value, U32.vals]
  simp only [iv, Vector.getElem_mk]
  simp only [List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ,
    Nat.reduceMod, Nat.cast_ofNat, Nat.reduceDiv, Nat.reducePow, List.map_toArray, List.map_cons, List.map_nil]
  simp only [Expression.eval]
  -- All these values are less than p, so ZMod.val gives back the original value
  have h1 : ZMod.val (58 : F p) = 58 := ZMod.val_cast_of_lt (by linarith [p_large_enough.elim] : 58 < p)
  have h2 : ZMod.val (245 : F p) = 245 := ZMod.val_cast_of_lt (by linarith [p_large_enough.elim] : 245 < p)
  have h3 : ZMod.val (79 : F p) = 79 := ZMod.val_cast_of_lt (by linarith [p_large_enough.elim] : 79 < p)
  have h4 : ZMod.val (165 : F p) = 165 := ZMod.val_cast_of_lt (by linarith [p_large_enough.elim] : 165 < p)
  rw [h1, h2, h3, h4]

-- Helper lemma for extracting elements from chaining_value evaluation
omit p_large_enough in
lemma eval_chaining_value_elem {env : Environment (F p)}
    {chaining_value_var : Vector (U32 (Expression (F p))) 8}
    {chaining_value : Vector (U32 (F p)) 8}
    (h_eval : (eval env chaining_value_var : ProvableVector _ _ _) = chaining_value)
    (i : Fin 8) :
    (eval env chaining_value_var[i]).value = chaining_value[i].value := by
  have h := congrArg (fun v => v[i]) h_eval
  simp only [eval_vector, Vector.getElem_map, circuit_norm] at h
  congr

theorem soundness : Soundness (F p) elaborated Assumptions Spec := by
  intro i0 env ⟨chaining_value_var, block_words_var, counter_high_var, counter_low_var, block_len_var, flags_var⟩
  intro ⟨chaining_value, block_words, counter_high, counter_low, block_len, flags⟩ h_input h_normalized h_holds

  -- dsimp [main, elaborated, circuit_norm, subcircuit_norm] at h_holds
  simp [circuit_norm] at h_input
  obtain ⟨h_eval_chaining_block_value, h_eval_block_words, h_eval_counter_high,
    h_eval_counter_low, h_eval_block_len, h_eval_flags⟩ := h_input

  simp only [circuit_norm, main, Spec]
  simp only [circuit_norm, main, subcircuit_norm] at h_holds
  simp only [Assumptions] at h_normalized

  -- Apply h_holds by proving its assumptions
  -- We need to prove that the state is normalized and the message is normalized

  -- First create a proper state vector variable
  let state_vec : Var BLAKE3State (F p) := #v[
    chaining_value_var[0], chaining_value_var[1], chaining_value_var[2], chaining_value_var[3],
    chaining_value_var[4], chaining_value_var[5], chaining_value_var[6], chaining_value_var[7],
    U32.decomposeNatExpr iv[0], U32.decomposeNatExpr iv[1], U32.decomposeNatExpr iv[2],
    U32.decomposeNatExpr iv[3], counter_low_var, counter_high_var, block_len_var, flags_var
  ]
  have state_vec_0_Normalized : (eval env chaining_value_var[0]).Normalized := by
    rw [getElem_eval_vector, h_eval_chaining_block_value]
    exact h_normalized.1 0
  have state_vec_1_Normalized : (eval env chaining_value_var[1]).Normalized := by
    rw [getElem_eval_vector, h_eval_chaining_block_value]
    exact h_normalized.1 1
  have state_vec_2_Normalized : (eval env chaining_value_var[2]).Normalized := by
    rw [getElem_eval_vector, h_eval_chaining_block_value]
    exact h_normalized.1 2
  have state_vec_3_Normalized : (eval env chaining_value_var[3]).Normalized := by
    rw [getElem_eval_vector, h_eval_chaining_block_value]
    exact h_normalized.1 3
  have state_vec_4_Normalized : (eval env chaining_value_var[4]).Normalized := by
    rw [getElem_eval_vector, h_eval_chaining_block_value]
    exact h_normalized.1 4
  have state_vec_5_Normalized : (eval env chaining_value_var[5]).Normalized := by
    rw [getElem_eval_vector, h_eval_chaining_block_value]
    exact h_normalized.1 5
  have state_vec_6_Normalized : (eval env chaining_value_var[6]).Normalized := by
    rw [getElem_eval_vector, h_eval_chaining_block_value]
    exact h_normalized.1 6
  have state_vec_7_Normalized : (eval env chaining_value_var[7]).Normalized := by
    rw [getElem_eval_vector, h_eval_chaining_block_value]
    exact h_normalized.1 7
  have state_vec_8_Normalized : (eval env (U32.decomposeNatExpr iv[0])).Normalized := by
    -- decomposeNatExpr produces a U32 of Expression.const values
    simp only [U32.decomposeNatExpr, U32.decomposeNat, eval, toVars, fromElements, toElements]
    simp only [Vector.map, Vector.getElem_mk, Expression.eval, U32.Normalized]
    -- Prove each limb is normalized
    have h (x : ℕ) : ZMod.val (n:=p) (x % 256 : ℕ) < 256 := by
      have : x % 256 < 256 := Nat.mod_lt _ (by norm_num)
      rw [FieldUtils.val_lt_p]
      assumption
      linarith [p_large_enough.elim]
    exact ⟨h _, h _, h _, h _⟩
  have state_vec_9_Normalized : (eval env (U32.decomposeNatExpr iv[1])).Normalized := by
    -- decomposeNatExpr produces a U32 of Expression.const values
    simp only [U32.decomposeNatExpr, U32.decomposeNat, eval, toVars, fromElements, toElements]
    simp only [Vector.map, Vector.getElem_mk, Expression.eval, U32.Normalized]
    -- Prove each limb is normalized
    have h (x : ℕ) : ZMod.val (n:=p) (x % 256 : ℕ) < 256 := by
      have : x % 256 < 256 := Nat.mod_lt _ (by norm_num)
      rw [FieldUtils.val_lt_p]
      assumption
      linarith [p_large_enough.elim]
    exact ⟨h _, h _, h _, h _⟩
  have state_vec_10_Normalized : (eval env (U32.decomposeNatExpr iv[2])).Normalized := by
    -- decomposeNatExpr produces a U32 of Expression.const values
    simp only [U32.decomposeNatExpr, U32.decomposeNat, eval, toVars, fromElements, toElements]
    simp only [Vector.map, Vector.getElem_mk, Expression.eval, U32.Normalized]
    -- Prove each limb is normalized
    have h (x : ℕ) : ZMod.val (n:=p) (x % 256 : ℕ) < 256 := by
      have : x % 256 < 256 := Nat.mod_lt _ (by norm_num)
      rw [FieldUtils.val_lt_p]
      assumption
      linarith [p_large_enough.elim]
    exact ⟨h _, h _, h _, h _⟩
  have state_vec_11_Normalized : (eval env (U32.decomposeNatExpr iv[3])).Normalized := by
    -- decomposeNatExpr produces a U32 of Expression.const values
    simp only [U32.decomposeNatExpr, U32.decomposeNat, eval, toVars, fromElements, toElements]
    simp only [Vector.map, Vector.getElem_mk, Expression.eval, U32.Normalized]
    -- Prove each limb is normalized
    have h (x : ℕ) : ZMod.val (n:=p) (x % 256 : ℕ) < 256 := by
      have : x % 256 < 256 := Nat.mod_lt _ (by norm_num)
      rw [FieldUtils.val_lt_p]
      assumption
      linarith [p_large_enough.elim]
    exact ⟨h _, h _, h _, h _⟩
  have state_vec_12_Normalized : (eval env counter_low_var).Normalized := by
    rw [h_eval_counter_low]
    exact h_normalized.2.2.2.1
  have state_vec_13_Normalized : (eval env counter_high_var).Normalized := by
    rw [h_eval_counter_high]
    exact h_normalized.2.2.1
  have state_vec_14_Normalized : (eval env block_len_var).Normalized := by
    rw [h_eval_block_len]
    exact h_normalized.2.2.2.2.1
  have state_vec_15_Normalized : (eval env flags_var).Normalized := by
    rw [h_eval_flags]
    exact h_normalized.2.2.2.2.2

  -- Show the state is normalized
  have h_state_normalized : (eval env state_vec).Normalized := by
    simp only [BLAKE3State.Normalized, state_vec, eval_vector]
    intro i
    fin_cases i
    -- First 8 elements are from chaining_value
    case «0» => (
      simp only [Vector.getElem_mk]; rw [Vector.getElem_map, getElem_eval_vector]
      simp only [eval_vector]
      simp only [Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil, Vector.getElem_mk,
        List.getElem_toArray, List.getElem_cons_zero, state_vec, state_vec_0_Normalized]
    )
    case «1» => (
      simp only [Vector.getElem_mk]; rw [Vector.getElem_map, getElem_eval_vector]
      simp only [eval_vector]
      simp only [Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil, Vector.getElem_mk,
        List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, state_vec, state_vec_1_Normalized]
    )
    case «2» => (
      simp only [Vector.getElem_mk]; rw [Vector.getElem_map, getElem_eval_vector]
      simp only [eval_vector]
      simp only [Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil, Vector.getElem_mk,
        List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, state_vec, state_vec_2_Normalized]
    )
    case «3» => (
      simp only [Vector.getElem_mk]; rw [Vector.getElem_map, getElem_eval_vector]
      simp only [eval_vector]
      simp only [Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil, Vector.getElem_mk,
        List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, state_vec, state_vec_3_Normalized]
    )
    case «4» => (
      simp only [Vector.getElem_mk]; rw [Vector.getElem_map, getElem_eval_vector]
      simp only [eval_vector]
      simp only [Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil, Vector.getElem_mk,
        List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, state_vec, state_vec_4_Normalized]
    )
    case «5» => (
      simp only [Vector.getElem_mk]; rw [Vector.getElem_map, getElem_eval_vector]
      simp only [eval_vector]
      simp only [Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil, Vector.getElem_mk,
        List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, state_vec, state_vec_5_Normalized]
    )
    case «6» => (
      simp only [Vector.getElem_mk]; rw [Vector.getElem_map, getElem_eval_vector]
      simp only [eval_vector]
      simp only [Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil, Vector.getElem_mk,
        List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, state_vec, state_vec_6_Normalized]
    )
    case «7» => (
      simp only [Vector.getElem_mk]; rw [Vector.getElem_map, getElem_eval_vector]
      simp only [eval_vector]
      simp only [Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil, Vector.getElem_mk,
        List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, state_vec, state_vec_7_Normalized]
    )
    -- Next 4 are IV constants
    case «8» => (
      simp only [Vector.getElem_mk]; rw [Vector.getElem_map]
      simp only [Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil, Vector.getElem_mk,
        List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, state_vec, state_vec_8_Normalized]
    )
    case «9» => (
      simp only [Vector.getElem_mk]; rw [Vector.getElem_map]
      simp only [Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil, Vector.getElem_mk,
        List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, state_vec, state_vec_9_Normalized]
    )
    case «10» => (
      simp only [Vector.getElem_mk]; rw [Vector.getElem_map]
      simp only [Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil, Vector.getElem_mk,
        List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, state_vec, state_vec_10_Normalized]
    )
    case «11» => (
      simp only [Vector.getElem_mk]; rw [Vector.getElem_map]
      simp only [Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil, Vector.getElem_mk,
        List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, state_vec, state_vec_11_Normalized]
    )
    -- Last 4 are counter_low, counter_high, block_len, flags
    case «12» => (
      simp only [Vector.getElem_mk]; rw [Vector.getElem_map]
      simp only [Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil, Vector.getElem_mk,
        List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, state_vec, state_vec_12_Normalized]
    )
    case «13» => (
      simp only [Vector.getElem_mk]; rw [Vector.getElem_map]
      simp only [Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil, Vector.getElem_mk,
        List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, state_vec, state_vec_13_Normalized]
    )
    case «14» => (
      simp only [Vector.getElem_mk]; rw [Vector.getElem_map]
      simp only [Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil, Vector.getElem_mk,
        List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, state_vec, state_vec_14_Normalized]
    )
    case «15» => (
      simp only [Vector.getElem_mk]; rw [Vector.getElem_map]
      simp only [Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil, Vector.getElem_mk,
        List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, state_vec, state_vec_15_Normalized]
    )

  -- Show the message is normalized
  have h_message_normalized : ∀ (i : Fin 16), (eval env block_words_var : BLAKE3State _)[i].Normalized := by
    intro i
    rw [h_eval_block_words]
    exact h_normalized.2.1 i

  -- Now we need to show that state_vec matches what's expected in h_holds
  have h_state_vec_eq : eval env state_vec = eval env {
    toArray := #[chaining_value_var[0], chaining_value_var[1], chaining_value_var[2], chaining_value_var[3],
                 chaining_value_var[4], chaining_value_var[5], chaining_value_var[6], chaining_value_var[7],
                 U32.decomposeNatExpr iv[0], U32.decomposeNatExpr iv[1], U32.decomposeNatExpr iv[2],
                 U32.decomposeNatExpr iv[3], counter_low_var, counter_high_var, block_len_var, flags_var],
    size_toArray := by simp
  } := by rfl

  have h_chaining_0_eq : (eval env chaining_value_var[0]).value = chaining_value[0].value := eval_chaining_value_elem h_eval_chaining_block_value 0
  have h_chaining_1_eq : (eval env chaining_value_var[1]).value = chaining_value[1].value := eval_chaining_value_elem h_eval_chaining_block_value 1
  have h_chaining_2_eq : (eval env chaining_value_var[2]).value = chaining_value[2].value := eval_chaining_value_elem h_eval_chaining_block_value 2
  have h_chaining_3_eq : (eval env chaining_value_var[3]).value = chaining_value[3].value := eval_chaining_value_elem h_eval_chaining_block_value 3
  have h_chaining_4_eq : (eval env chaining_value_var[4]).value = chaining_value[4].value := eval_chaining_value_elem h_eval_chaining_block_value 4
  have h_chaining_5_eq : (eval env chaining_value_var[5]).value = chaining_value[5].value := eval_chaining_value_elem h_eval_chaining_block_value 5
  have h_chaining_6_eq : (eval env chaining_value_var[6]).value = chaining_value[6].value := eval_chaining_value_elem h_eval_chaining_block_value 6
  have h_chaining_7_eq : (eval env chaining_value_var[7]).value = chaining_value[7].value := eval_chaining_value_elem h_eval_chaining_block_value 7

  -- Equations for IV constants (using the external lemmas)
  have h_iv_0_eq := eval_decomposeNatExpr_iv_0 env
  have h_iv_1_eq := eval_decomposeNatExpr_iv_1 env
  have h_iv_2_eq := eval_decomposeNatExpr_iv_2 env
  have h_iv_3_eq := eval_decomposeNatExpr_iv_3 env

  -- Equations for counter values
  have h_counter_low_eq : counter_low.value % 4294967296 = counter_low.value := by
    apply Nat.mod_eq_of_lt
    exact U32.value_lt_of_normalized h_normalized.2.2.2.1
  have h_counter_high_eq : (counter_low.value + 4294967296 * counter_high.value) / 4294967296 = counter_high.value := by
    -- We want to show (counter_low.value + 2^32 * counter_high.value) / 2^32 = counter_high.value
    -- Since counter_low.value < 2^32, this follows from properties of division
    have h1 : counter_low.value < 4294967296 := U32.value_lt_of_normalized h_normalized.2.2.2.1
    have h2 : 4294967296 > 0 := by norm_num
    -- Now we have (2^32 * counter_high.value + counter_low.value) / 2^32
    -- This equals counter_high.value + counter_low.value / 2^32
    rw [Nat.add_mul_div_left _ _ h2]
    rw [Nat.div_eq_of_lt h1]
    simp

  -- Apply h_holds with the proven assumptions
  rw [← h_state_vec_eq] at h_state_normalized
  have h_spec := h_holds ⟨h_state_normalized, h_message_normalized⟩
  clear h_holds

  -- Now we need to show that the spec holds
  -- h_spec tells us that sevenRoundsApplyStyle.Spec holds for the inputs and output
  -- We need to unpack what this means and relate it to our Spec

  simp only [sevenRoundsApplyStyle, FormalCircuit.weakenSpec, sevenRoundsFinal,
             FormalCircuit.concat] at h_spec

  -- The spec for sevenRoundsApplyStyle says the output equals applySevenRounds
  simp only [SevenRoundsSpec] at h_spec

  obtain ⟨h_value, h_normalized⟩ := h_spec

  constructor
  · -- Show out.value = applyRounds ...
    -- Use our lemma to express applyRounds in terms of applySevenRounds
    rw [applyRounds_eq_applySevenRounds]

    -- h_value tells us the output equals applySevenRounds on our constructed state
    simp only [BLAKE3State.value] at h_value ⊢
    calc
      _ = _ := h_value
      _ = _ := by
        clear h_value
        rw [h_eval_block_words]
        simp only[eval_vector]
        simp only [Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil, Vector.getElem_map,
          Nat.reducePow, Nat.add_mul_mod_self_left, state_vec, h_eval_chaining_block_value, h_eval_block_words, h_eval_counter_high, h_eval_counter_low, h_eval_block_len, h_eval_flags]
        simp only [h_chaining_0_eq, h_chaining_1_eq, h_chaining_2_eq, h_chaining_3_eq, h_chaining_4_eq, h_chaining_5_eq,
          h_chaining_6_eq, h_chaining_7_eq]
        simp only [h_iv_0_eq, h_iv_1_eq, h_iv_2_eq, h_iv_3_eq]
        simp only [h_counter_low_eq, h_counter_high_eq]

  · -- Show out.Normalized
    exact h_normalized

theorem completeness : Completeness (F p) elaborated Assumptions := by
  intro i0 env ⟨chaining_value_var, block_words_var, counter_high_var, counter_low_var, block_len_var, flags_var⟩
  intro henv ⟨chaining_value, block_words, counter_high, counter_low, block_len, flags⟩ h_input h_normalized

  -- Simplify goal using circuit_norm and use sevenRoundsApplyStyle completeness
  simp only [circuit_norm, main, subcircuit_norm] at henv ⊢

  simp [circuit_norm] at h_input
  obtain ⟨h_eval_chaining_block_value, h_eval_block_words, h_eval_counter_high,
    h_eval_counter_low, h_eval_block_len, h_eval_flags⟩ := h_input

  -- Create the state vector variable
  let state_vec : Var BLAKE3State (F p) := #v[
    chaining_value_var[0], chaining_value_var[1], chaining_value_var[2], chaining_value_var[3],
    chaining_value_var[4], chaining_value_var[5], chaining_value_var[6], chaining_value_var[7],
    U32.decomposeNatExpr iv[0], U32.decomposeNatExpr iv[1], U32.decomposeNatExpr iv[2],
    U32.decomposeNatExpr iv[3], counter_low_var, counter_high_var, block_len_var, flags_var
  ]
  have state_vec_0_Normalized : (eval env chaining_value_var[0]).Normalized := by
    rw [getElem_eval_vector, h_eval_chaining_block_value]
    exact h_normalized.1 0
  have state_vec_1_Normalized : (eval env chaining_value_var[1]).Normalized := by
    rw [getElem_eval_vector, h_eval_chaining_block_value]
    exact h_normalized.1 1
  have state_vec_2_Normalized : (eval env chaining_value_var[2]).Normalized := by
    rw [getElem_eval_vector, h_eval_chaining_block_value]
    exact h_normalized.1 2
  have state_vec_3_Normalized : (eval env chaining_value_var[3]).Normalized := by
    rw [getElem_eval_vector, h_eval_chaining_block_value]
    exact h_normalized.1 3
  have state_vec_4_Normalized : (eval env chaining_value_var[4]).Normalized := by
    rw [getElem_eval_vector, h_eval_chaining_block_value]
    exact h_normalized.1 4
  have state_vec_5_Normalized : (eval env chaining_value_var[5]).Normalized := by
    rw [getElem_eval_vector, h_eval_chaining_block_value]
    exact h_normalized.1 5
  have state_vec_6_Normalized : (eval env chaining_value_var[6]).Normalized := by
    rw [getElem_eval_vector, h_eval_chaining_block_value]
    exact h_normalized.1 6
  have state_vec_7_Normalized : (eval env chaining_value_var[7]).Normalized := by
    rw [getElem_eval_vector, h_eval_chaining_block_value]
    exact h_normalized.1 7
  have state_vec_8_Normalized : (eval env (U32.decomposeNatExpr iv[0])).Normalized := by
    -- decomposeNatExpr produces a U32 of Expression.const values
    simp only [U32.decomposeNatExpr, U32.decomposeNat, eval, toVars, fromElements, toElements]
    simp only [Vector.map, Vector.getElem_mk, Expression.eval, U32.Normalized]
    -- Prove each limb is normalized
    have h (x : ℕ) : ZMod.val (n:=p) (x % 256 : ℕ) < 256 := by
      have : x % 256 < 256 := Nat.mod_lt _ (by norm_num)
      rw [FieldUtils.val_lt_p]
      assumption
      linarith [p_large_enough.elim]
    exact ⟨h _, h _, h _, h _⟩
  have state_vec_9_Normalized : (eval env (U32.decomposeNatExpr iv[1])).Normalized := by
    -- decomposeNatExpr produces a U32 of Expression.const values
    simp only [U32.decomposeNatExpr, U32.decomposeNat, eval, toVars, fromElements, toElements]
    simp only [Vector.map, Vector.getElem_mk, Expression.eval, U32.Normalized]
    -- Prove each limb is normalized
    have h (x : ℕ) : ZMod.val (n:=p) (x % 256 : ℕ) < 256 := by
      have : x % 256 < 256 := Nat.mod_lt _ (by norm_num)
      rw [FieldUtils.val_lt_p]
      assumption
      linarith [p_large_enough.elim]
    exact ⟨h _, h _, h _, h _⟩
  have state_vec_10_Normalized : (eval env (U32.decomposeNatExpr iv[2])).Normalized := by
    -- decomposeNatExpr produces a U32 of Expression.const values
    simp only [U32.decomposeNatExpr, U32.decomposeNat, eval, toVars, fromElements, toElements]
    simp only [Vector.map, Vector.getElem_mk, Expression.eval, U32.Normalized]
    -- Prove each limb is normalized
    have h (x : ℕ) : ZMod.val (n:=p) (x % 256 : ℕ) < 256 := by
      have : x % 256 < 256 := Nat.mod_lt _ (by norm_num)
      rw [FieldUtils.val_lt_p]
      assumption
      linarith [p_large_enough.elim]
    exact ⟨h _, h _, h _, h _⟩
  have state_vec_11_Normalized : (eval env (U32.decomposeNatExpr iv[3])).Normalized := by
    -- decomposeNatExpr produces a U32 of Expression.const values
    simp only [U32.decomposeNatExpr, U32.decomposeNat, eval, toVars, fromElements, toElements]
    simp only [Vector.map, Vector.getElem_mk, Expression.eval, U32.Normalized]
    -- Prove each limb is normalized
    have h (x : ℕ) : ZMod.val (n:=p) (x % 256 : ℕ) < 256 := by
      have : x % 256 < 256 := Nat.mod_lt _ (by norm_num)
      rw [FieldUtils.val_lt_p]
      assumption
      linarith [p_large_enough.elim]
    exact ⟨h _, h _, h _, h _⟩
  have state_vec_12_Normalized : (eval env counter_low_var).Normalized := by
    rw [h_eval_counter_low]
    exact h_normalized.2.2.2.1
  have state_vec_13_Normalized : (eval env counter_high_var).Normalized := by
    rw [h_eval_counter_high]
    exact h_normalized.2.2.1
  have state_vec_14_Normalized : (eval env block_len_var).Normalized := by
    rw [h_eval_block_len]
    exact h_normalized.2.2.2.2.1
  have state_vec_15_Normalized : (eval env flags_var).Normalized := by
    rw [h_eval_flags]
    exact h_normalized.2.2.2.2.2

  -- Show the state is normalized
  have h_state_normalized : (eval env state_vec).Normalized := by
    simp only [BLAKE3State.Normalized, state_vec, eval_vector]
    intro i
    fin_cases i
    -- First 8 elements are from chaining_value
    case «0» => (
      simp only [Vector.getElem_mk]; rw [Vector.getElem_map, getElem_eval_vector]
      simp only [eval_vector]
      simp only [Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil, Vector.getElem_mk,
        List.getElem_toArray, List.getElem_cons_zero, state_vec, state_vec_0_Normalized]
    )
    case «1» => (
      simp only [Vector.getElem_mk]; rw [Vector.getElem_map, getElem_eval_vector]
      simp only [eval_vector]
      simp only [Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil, Vector.getElem_mk,
        List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, state_vec, state_vec_1_Normalized]
    )
    case «2» => (
      simp only [Vector.getElem_mk]; rw [Vector.getElem_map, getElem_eval_vector]
      simp only [eval_vector]
      simp only [Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil, Vector.getElem_mk,
        List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, state_vec, state_vec_2_Normalized]
    )
    case «3» => (
      simp only [Vector.getElem_mk]; rw [Vector.getElem_map, getElem_eval_vector]
      simp only [eval_vector]
      simp only [Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil, Vector.getElem_mk,
        List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, state_vec, state_vec_3_Normalized]
    )
    case «4» => (
      simp only [Vector.getElem_mk]; rw [Vector.getElem_map, getElem_eval_vector]
      simp only [eval_vector]
      simp only [Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil, Vector.getElem_mk,
        List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, state_vec, state_vec_4_Normalized]
    )
    case «5» => (
      simp only [Vector.getElem_mk]; rw [Vector.getElem_map, getElem_eval_vector]
      simp only [eval_vector]
      simp only [Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil, Vector.getElem_mk,
        List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, state_vec, state_vec_5_Normalized]
    )
    case «6» => (
      simp only [Vector.getElem_mk]; rw [Vector.getElem_map, getElem_eval_vector]
      simp only [eval_vector]
      simp only [Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil, Vector.getElem_mk,
        List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, state_vec, state_vec_6_Normalized]
    )
    case «7» => (
      simp only [Vector.getElem_mk]; rw [Vector.getElem_map, getElem_eval_vector]
      simp only [eval_vector]
      simp only [Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil, Vector.getElem_mk,
        List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, state_vec, state_vec_7_Normalized]
    )
    -- Next 4 are IV constants
    case «8» => (
      simp only [Vector.getElem_mk]; rw [Vector.getElem_map]
      simp only [Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil, Vector.getElem_mk,
        List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, state_vec, state_vec_8_Normalized]
    )
    case «9» => (
      simp only [Vector.getElem_mk]; rw [Vector.getElem_map]
      simp only [Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil, Vector.getElem_mk,
        List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, state_vec, state_vec_9_Normalized]
    )
    case «10» => (
      simp only [Vector.getElem_mk]; rw [Vector.getElem_map]
      simp only [Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil, Vector.getElem_mk,
        List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, state_vec, state_vec_10_Normalized]
    )
    case «11» => (
      simp only [Vector.getElem_mk]; rw [Vector.getElem_map]
      simp only [Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil, Vector.getElem_mk,
        List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, state_vec, state_vec_11_Normalized]
    )
    -- Last 4 are counter_low, counter_high, block_len, flags
    case «12» => (
      simp only [Vector.getElem_mk]; rw [Vector.getElem_map]
      simp only [Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil, Vector.getElem_mk,
        List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, state_vec, state_vec_12_Normalized]
    )
    case «13» => (
      simp only [Vector.getElem_mk]; rw [Vector.getElem_map]
      simp only [Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil, Vector.getElem_mk,
        List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, state_vec, state_vec_13_Normalized]
    )
    case «14» => (
      simp only [Vector.getElem_mk]; rw [Vector.getElem_map]
      simp only [Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil, Vector.getElem_mk,
        List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, state_vec, state_vec_14_Normalized]
    )
    case «15» => (
      simp only [Vector.getElem_mk]; rw [Vector.getElem_map]
      simp only [Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil, Vector.getElem_mk,
        List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, state_vec, state_vec_15_Normalized]
    )

  -- Show the message is normalized
  have h_message_normalized : ∀ (i : Fin 16), (eval env block_words_var : BLAKE3State _)[i].Normalized := by
    intro i
    rw [h_eval_block_words]
    exact h_normalized.2.1 i

  constructor
  · apply h_state_normalized
  · apply h_message_normalized


def circuit : FormalCircuit (F p) Inputs BLAKE3State := {
  elaborated with Assumptions, Spec, soundness, completeness
}

end Gadgets.BLAKE3.ApplyRounds
