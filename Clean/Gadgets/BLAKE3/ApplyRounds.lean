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
  Circuit.FormalCircuit.concat roundWithPermute roundWithPermute (by
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
  let state ← subcircuit Round.circuit ⟨state, block_words⟩
  let block_words ← subcircuit Permute.circuit block_words

  let state ← subcircuit Round.circuit ⟨state, block_words⟩
  let block_words ← subcircuit Permute.circuit block_words

  let state ← subcircuit Round.circuit ⟨state, block_words⟩
  let block_words ← subcircuit Permute.circuit block_words

  let state ← subcircuit Round.circuit ⟨state, block_words⟩
  let block_words ← subcircuit Permute.circuit block_words

  let state ← subcircuit Round.circuit ⟨state, block_words⟩
  let block_words ← subcircuit Permute.circuit block_words

  let state ← subcircuit Round.circuit ⟨state, block_words⟩
  let block_words ← subcircuit Permute.circuit block_words

  let state ← subcircuit Round.circuit ⟨state, block_words⟩
  let block_words ← subcircuit Permute.circuit block_words

  let state ← subcircuit Round.circuit ⟨state, block_words⟩
  let block_words ← subcircuit Permute.circuit block_words

  let state ← subcircuit Round.circuit ⟨state, block_words⟩

  return state

#eval! main (p:=pBabybear) default |>.localLength
-- #eval! main (p:=pBabybear) default |>.output
instance elaborated : ElaboratedCircuit (F p) Inputs BLAKE3State where
  main := main
  localLength _ := 6912
  localLength_eq input i0 := by
    dsimp only [main, Round.circuit, Permute.circuit, Circuit.pure_def, Circuit.bind_def,
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

theorem soundness : Soundness (F p) elaborated Assumptions Spec := by
  intro i0 env ⟨chaining_value_var, block_words_var, counter_high_var, counter_low_var, block_len_var, flags_var⟩
  intro ⟨chaining_value, block_words, counter_high, counter_low, block_len, flags⟩ h_input h_normalized h_holds

  -- dsimp [main, elaborated, circuit_norm, subcircuit_norm] at h_holds
  simp [circuit_norm] at h_input
  obtain ⟨h_eval_chaining_block_value, h_eval_block_words, h_eval_counter_high,
    h_eval_counter_low, h_eval_block_len, h_eval_flags⟩ := h_input

  obtain ⟨round1, h_holds⟩ := h_holds

  simp [circuit_norm, subcircuit_norm, Round.circuit, Round.Assumptions, Round.Spec] at round1

  rw [eval_vector, BLAKE3State.Normalized] at round1
  -- prove all the assumptions of the first round invocation
  specialize round1 (by
    simp [eval_vector, BLAKE3State.Normalized, Fin.forall_fin_succ]
    sorry)
  specialize round1 sorry

  -- permute 1
  obtain ⟨permute1, h_holds⟩ := h_holds
  simp [circuit_norm, subcircuit_norm, Permute.circuit, Permute.Assumptions, Permute.Spec] at permute1
  specialize permute1 sorry

  -- round 2
  obtain ⟨round2, h_holds⟩ := h_holds
  simp [circuit_norm, subcircuit_norm, Round.circuit, Round.Assumptions, Round.Spec] at round2
  rw [round1.left] at round2
  specialize round2 round1.right permute1.right

  -- permute 2
  obtain ⟨permute2, h_holds⟩ := h_holds
  simp [circuit_norm, subcircuit_norm, Permute.circuit, Permute.Assumptions, Permute.Spec] at permute2
  rw [permute1.left] at permute2
  specialize permute2 permute1.right

  sorry

theorem completeness : Completeness (F p) elaborated Assumptions := by
  sorry

def circuit : FormalCircuit (F p) Inputs BLAKE3State := {
  elaborated with Assumptions, Spec, soundness, completeness
}

end Gadgets.BLAKE3.ApplyRounds
