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
    intros
    simp_all only [roundWithPermute, Round.Assumptions]
    aesop
  ) (by aesop)

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
    simp_all only [roundWithPermute, TwoRoundsSpec, applyTwoRounds]

    constructor
    · rfl
    constructor <;> aesop
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
    constructor <;> aesop
  ) (by aesop)

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
    constructor <;> aesop
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
    constructor <;> aesop
  ) (by aesop)

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
    aesop
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
    simp_all [sixRoundsApplyStyle, FormalCircuit.weakenSpec, SixRoundsSpec, Round.circuit, Round.Assumptions]
  ) (by aesop)

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
    rintro input output h_assumptions ⟨mid, h_spec1, h_spec2⟩
    -- Break down the specs similar to previous proofs
    simp_all only [sixRoundsApplyStyle, FormalCircuit.weakenSpec, SixRoundsSpec, Round.circuit, Round.Spec, SevenRoundsSpec, applySevenRounds, applySixRounds]
    aesop
  )

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
        iv[0].toNat, iv[1].toNat, iv[2].toNat, iv[3].toNat,
        counter % 2^32, counter / 2^32, block_len, flags
      ])
      block_words := by
  -- applyRounds constructs the same initial state and then applies 7 rounds
  simp only [applyRounds, applySevenRounds]

lemma eval_decomposeNatExpr_small (env : Environment (F p)) (x : ℕ) :
    x < 256^4 ->
    (eval env (U32.decomposeNatExpr x)).value = x := by
  intro _
  simp only [U32.decomposeNatExpr]
  apply U32.value_of_decomposedNat_of_small
  assumption

lemma eval_fromUInt32_value (env : Environment (F p)) (x : UInt32) :
    (eval env (const (U32.fromUInt32 x))).value = x.toNat := by
  refine eval_decomposeNatExpr_small env x.toNat ?_
  have := UInt32.toNat_lt_size x
  omega

-- Tactic for common steps in state vector normalization proof
syntax "state_vec_norm_simp" : tactic
macro_rules
  | `(tactic| state_vec_norm_simp) => `(tactic|
      simp only [Vector.getElem_mk];
      rw [Vector.getElem_map, getElem_eval_vector];
      simp only [eval_vector];
      simp only [Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil, Vector.getElem_mk,
        List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero])

-- Tactic for cases 8-15 which don't use getElem_eval_vector
syntax "state_vec_norm_simp_simple" : tactic
macro_rules
  | `(tactic| state_vec_norm_simp_simple) => `(tactic|
      simp only [Vector.getElem_mk];
      rw [Vector.getElem_map];
      simp only [Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil, Vector.getElem_mk,
        List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero])

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
    const (U32.fromUInt32 iv[0]), const (U32.fromUInt32 iv[1]),
    const (U32.fromUInt32 iv[2]), const (U32.fromUInt32 iv[3]),
    counter_low, counter_high, block_len, flags
  ]

  -- Apply 7 rounds with message permutation between rounds (except the last)
  sevenRoundsApplyStyle ⟨state, block_words⟩

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
    U32.decomposeNatExpr iv[0].toNat, U32.decomposeNatExpr iv[1].toNat, U32.decomposeNatExpr iv[2].toNat,
    U32.decomposeNatExpr iv[3].toNat, counter_low_var, counter_high_var, block_len_var, flags_var
  ]
  -- Helper to prove normalization of chaining value elements
  have h_chaining_value_normalized : ∀ (i : Fin 8), (eval env chaining_value_var[i]).Normalized := by
    rintro ⟨ i, h_i ⟩
    have h : (eval env chaining_value_var : ProvableVector _ _ _) = chaining_value := h_eval_chaining_block_value
    have h_i : (eval env chaining_value_var : ProvableVector _ _ _)[i] = chaining_value[i] := by
      rw [h]
    simp only [eval_vector, Vector.getElem_map] at h_i
    convert h_normalized.1 i
    simp_all only [circuit_norm]
    congr
    norm_num
    omega
  have state_vec_8_Normalized : (eval env (U32.decomposeNatExpr iv[0].toNat)).Normalized := by
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
  have state_vec_9_Normalized : (eval env (U32.decomposeNatExpr iv[1].toNat)).Normalized := by
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
  have state_vec_10_Normalized : (eval env (U32.decomposeNatExpr iv[2].toNat)).Normalized := by
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
  have state_vec_11_Normalized : (eval env (U32.decomposeNatExpr iv[3].toNat)).Normalized := by
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
    case «0» => state_vec_norm_simp; exact h_chaining_value_normalized 0
    case «1» => state_vec_norm_simp; exact h_chaining_value_normalized 1
    case «2» => state_vec_norm_simp; exact h_chaining_value_normalized 2
    case «3» => state_vec_norm_simp; exact h_chaining_value_normalized 3
    case «4» => state_vec_norm_simp; exact h_chaining_value_normalized 4
    case «5» => state_vec_norm_simp; exact h_chaining_value_normalized 5
    case «6» => state_vec_norm_simp; exact h_chaining_value_normalized 6
    case «7» => state_vec_norm_simp; exact h_chaining_value_normalized 7
    -- Next 4 are IV constants
    case «8» => state_vec_norm_simp_simple; simp only [state_vec, state_vec_8_Normalized]
    case «9» => state_vec_norm_simp_simple; simp only [state_vec, state_vec_9_Normalized]
    case «10» => state_vec_norm_simp_simple; simp only [state_vec, state_vec_10_Normalized]
    case «11» => state_vec_norm_simp_simple; simp only [state_vec, state_vec_11_Normalized]
    -- Last 4 are counter_low, counter_high, block_len, flags
    case «12» => state_vec_norm_simp_simple; simp only [state_vec, state_vec_12_Normalized]
    case «13» => state_vec_norm_simp_simple; simp only [state_vec, state_vec_13_Normalized]
    case «14» => state_vec_norm_simp_simple; simp only [state_vec, state_vec_14_Normalized]
    case «15» => state_vec_norm_simp_simple; simp only [state_vec, state_vec_15_Normalized]

  -- Show the message is normalized
  have h_message_normalized : ∀ (i : Fin 16), (eval env block_words_var : BLAKE3State _)[i].Normalized := by
    intro i
    rw [h_eval_block_words]
    exact h_normalized.2.1 i

  -- Now we need to show that state_vec matches what's expected in h_holds
  have h_state_vec_eq : eval env state_vec = eval env {
    toArray := #[chaining_value_var[0], chaining_value_var[1], chaining_value_var[2], chaining_value_var[3],
                 chaining_value_var[4], chaining_value_var[5], chaining_value_var[6], chaining_value_var[7],
                 U32.decomposeNatExpr iv[0].toNat, U32.decomposeNatExpr iv[1].toNat, U32.decomposeNatExpr iv[2].toNat,
                 U32.decomposeNatExpr iv[3].toNat, counter_low_var, counter_high_var, block_len_var, flags_var],
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
        simp [h_chaining_0_eq, h_chaining_1_eq, h_chaining_2_eq, h_chaining_3_eq, h_chaining_4_eq, h_chaining_5_eq,
          h_chaining_6_eq, h_chaining_7_eq, eval_fromUInt32_value, h_counter_low_eq, h_counter_high_eq]

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
    const (U32.fromUInt32 iv[0]), const (U32.fromUInt32 iv[1]), const (U32.fromUInt32 iv[2]),
    const (U32.fromUInt32 iv[3]), counter_low_var, counter_high_var, block_len_var, flags_var
  ]
  -- Helper to prove normalization of chaining value elements
  have h_chaining_value_normalized : ∀ (i : Fin 8), (eval env chaining_value_var[i]).Normalized := by
    rintro ⟨ i, h_i ⟩
    have h : (eval env chaining_value_var : ProvableVector _ _ _) = chaining_value := h_eval_chaining_block_value
    have h_i : (eval env chaining_value_var : ProvableVector _ _ _)[i] = chaining_value[i] := by
      rw [h]
    simp only [eval_vector, Vector.getElem_map] at h_i
    convert h_normalized.1 i
    simp_all only [circuit_norm]
    congr
    norm_num
    omega
  have state_vec_8_Normalized : (eval env (const (U32.fromUInt32 iv[0]))).Normalized := by
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
  have state_vec_9_Normalized : (eval env (const (U32.fromUInt32 iv[1]))).Normalized := by
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
  have state_vec_10_Normalized : (eval env (const (U32.fromUInt32 iv[2]))).Normalized := by
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
  have state_vec_11_Normalized : (eval env (const (U32.fromUInt32 iv[3]))).Normalized := by
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
    case «0» => state_vec_norm_simp; exact h_chaining_value_normalized 0
    case «1» => state_vec_norm_simp; exact h_chaining_value_normalized 1
    case «2» => state_vec_norm_simp; exact h_chaining_value_normalized 2
    case «3» => state_vec_norm_simp; exact h_chaining_value_normalized 3
    case «4» => state_vec_norm_simp; exact h_chaining_value_normalized 4
    case «5» => state_vec_norm_simp; exact h_chaining_value_normalized 5
    case «6» => state_vec_norm_simp; exact h_chaining_value_normalized 6
    case «7» => state_vec_norm_simp; exact h_chaining_value_normalized 7
    -- Next 4 are IV constants
    case «8» => state_vec_norm_simp_simple; simp only [state_vec, state_vec_8_Normalized]
    case «9» => state_vec_norm_simp_simple; simp only [state_vec, state_vec_9_Normalized]
    case «10» => state_vec_norm_simp_simple; simp only [state_vec, state_vec_10_Normalized]
    case «11» => state_vec_norm_simp_simple; simp only [state_vec, state_vec_11_Normalized]
    -- Last 4 are counter_low, counter_high, block_len, flags
    case «12» => state_vec_norm_simp_simple; simp only [state_vec, state_vec_12_Normalized]
    case «13» => state_vec_norm_simp_simple; simp only [state_vec, state_vec_13_Normalized]
    case «14» => state_vec_norm_simp_simple; simp only [state_vec, state_vec_14_Normalized]
    case «15» => state_vec_norm_simp_simple; simp only [state_vec, state_vec_15_Normalized]

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
