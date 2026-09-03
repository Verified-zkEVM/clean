import Clean.Gadgets.BLAKE3.BLAKE3State
import Clean.Gadgets.BLAKE3.Round
import Clean.Gadgets.BLAKE3.Permute
import Clean.Types.U32
import Clean.Circuit.Provable
import Clean.Specs.BLAKE3
import Clean.Circuit.StructuralLemmas
import Clean.Utils.Tactics

namespace Gadgets.BLAKE3.ApplyRounds
variable {p : ℕ} [Fact p.Prime] [p_large_enough: Fact (p > 2^16 + 2^8)]
instance : Fact (p > 512) := .mk (by linarith [p_large_enough.elim])

open Specs.BLAKE3 (applyRounds iv round permute)

/--
Lemma to handle the notational difference between BLAKE3State.value and Vector.map U32.value.
-/
lemma blake3_value_eq_map_value {p : ℕ} (msg : Vector (U32 (F p)) 16) :
  BLAKE3State.value msg = Vector.map U32.value msg := rfl

open Specs.BLAKE3 (msgPermutation) in
def output (input : Var Round.Inputs (F p)) (offset : ℕ) : Var Round.Inputs (F p) :=
  { state := Round.circuit.output input offset,
    message := Vector.ofFn fun i ↦ input.message[msgPermutation[i]] }

/--
A FormalCircuit that performs one round followed by permuting the message.
Both input and output are Round.Inputs (state and message).

The spec follows the pattern from the applyRounds function:
- Apply round to get new state
- Permute the message
-/
def roundWithPermute : FormalCircuit (F p) Round.Inputs Round.Inputs where
  main input := do
    let state ← Round.circuit input
    let permuted_message ← Permute.circuit input.message
    return ⟨state, permuted_message⟩

  elaborated := by elaborate_circuit_with {
    output input offset := output input offset
  }

  Assumptions := Round.Assumptions
  Spec input output :=
    let state' := round input.state.value (BLAKE3State.value input.message)
    output.state.value = state' ∧
    output.state.Normalized ∧
    BLAKE3State.value output.message = permute (BLAKE3State.value input.message) ∧
    BLAKE3State.Normalized output.message

  soundness := by
    circuit_proof_start [Round.circuit, Permute.circuit,
      Round.Assumptions, Permute.Assumptions, Round.Spec, Permute.Spec]
    rcases h_holds with ⟨ h_holds1, h_holds2 ⟩
    specialize h_holds1 h_assumptions
    specialize h_holds2 h_assumptions.right
    exact ⟨ h_holds1.1, h_holds1.2, h_holds2 ⟩
  completeness := by
    circuit_proof_start [Round.circuit, Permute.circuit,
      Round.Assumptions, Permute.Assumptions]
    exact ⟨ h_assumptions, h_assumptions.right ⟩

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
def applyTwoRounds (state : Vector ℕ 16) (message : Vector ℕ 16) : Vector ℕ 16 × Vector ℕ 16 :=
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
    intro input mid h_assumptions h_spec
    -- twoRoundsWithPermute.Spec says ∃ mid', roundWithPermute.Spec input mid' ∧ roundWithPermute.Spec mid' mid
    obtain ⟨mid', h_spec1, h_spec2⟩ := h_spec
    -- We need to show twoRoundsWithPermute.Assumptions mid
    -- which is the same as roundWithPermute.Assumptions mid, which is Round.Assumptions mid
    simp only [twoRoundsWithPermute, roundWithPermute] at h_spec2 ⊢
    constructor <;> aesop
  ) (by simp +instances [circuit_norm, twoRoundsWithPermute, roundWithPermute,
    Round.circuit, Permute.circuit])

/--
Apply four rounds of BLAKE3 compression, starting from a Round.Inputs state.
This follows the same pattern as applyRounds but for only 4 rounds:
- First round, permute message
- Second round, permute message
- Third round, permute message
- Fourth round, permute message
Returns the final state and permuted message.
-/
def applyFourRounds (state : Vector ℕ 16) (message : Vector ℕ 16) : Vector ℕ 16 × Vector ℕ 16 :=
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
    simp only [FourRoundsSpec, applyFourRounds]

    constructor
    · simp_all only
      congr
    · aesop
  )

/--
Combines six rounds with permutation using fourRoundsWithPermute and twoRoundsWithPermute.
This performs six rounds with message permutation between them.
-/
def sixRoundsWithPermute : FormalCircuit (F p) Round.Inputs Round.Inputs :=
  fourRoundsWithPermute.concat twoRoundsWithPermute (by
    -- Prove compatibility: if fourRoundsWithPermute assumptions and spec hold,
    -- then twoRoundsWithPermute assumptions hold
    intro input mid h_assumptions h_spec
    -- fourRoundsWithPermute.Spec says ∃ mid', twoRoundsWithPermute.Spec ... ∧ twoRoundsWithPermute.Spec ...
    obtain ⟨mid', h_spec1, h_spec2⟩ := h_spec
    -- Each twoRoundsWithPermute.Spec says ∃ mid'', roundWithPermute.Spec ... ∧ roundWithPermute.Spec ...
    obtain ⟨mid'', h_spec2_1, h_spec2_2⟩ := h_spec2
    -- We need to show twoRoundsWithPermute.Assumptions mid
    -- which is the same as roundWithPermute.Assumptions mid, which is Round.Assumptions mid
    simp only [twoRoundsWithPermute, roundWithPermute] at h_spec2_2 ⊢
    constructor <;> aesop
  ) (by simp +instances [circuit_norm, twoRoundsWithPermute, roundWithPermute,
    Round.circuit, Permute.circuit])

/--
Apply six rounds of BLAKE3 compression, starting from a Round.Inputs state.
This follows the same pattern as applyRounds but for only 6 rounds:
- First through sixth rounds, each followed by permute message
Returns the final state and permuted message.
-/
def applySixRounds (state : Vector ℕ 16) (message : Vector ℕ 16) : Vector ℕ 16 × Vector ℕ 16 :=
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
    and_intros
    · simp_all only
      congr
    · aesop
    · aesop
    · aesop
  )

/--
Seven rounds with permutation: combines sixRoundsApplyStyle with a final round.
This represents the complete 7-round BLAKE3 compression function.
-/
def sevenRoundsFinal : FormalCircuit (F p) Round.Inputs BLAKE3State :=
  sixRoundsApplyStyle.concat Round.circuit (by
    -- Prove compatibility: sixRoundsApplyStyle output satisfies Round.circuit assumptions
    intro input mid h_assumptions h_spec
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
def applySevenRounds (state : Vector ℕ 16) (message : Vector ℕ 16) : Vector ℕ 16 :=
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
    (chaining_value : Vector ℕ 8)
    (block_words : Vector ℕ 16)
    (counter : ℕ)
    (block_len : ℕ)
    (flags : ℕ) :
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
    x < 256^4 →
    (eval env (U32.decomposeNatExpr (p:=p) x)).value = x := by
  intro h
  simp only [U32.decomposeNatExpr, circuit_norm]
  exact U32.value_of_decomposedNat_of_small x h

-- Tactic for common steps in state vector normalization proof
syntax "state_vec_norm_simp" : tactic
macro_rules
  | `(tactic| state_vec_norm_simp) => `(tactic|
      simp only [Vector.getElem_mk];
      rw [Vector.getElem_map, getElem_eval_vector];
      simp only [eval_vector, Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil, Vector.getElem_mk,
        List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero])

-- Tactic for cases 8-15 which don't use getElem_eval_vector
syntax "state_vec_norm_simp_simple" : tactic
macro_rules
  | `(tactic| state_vec_norm_simp_simple) => `(tactic|
      simp only [Vector.getElem_mk, Vector.getElem_map, Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil, Vector.getElem_mk,
        List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, circuit_norm, U32.fromUInt32_normalized])

structure Inputs (F : Type) where
  chaining_value : Vector (U32 F) 8
  block_words : Vector (U32 F) 16
  counter_high : U32 F
  counter_low : U32 F
  block_len : U32 F
  flags : U32 F
deriving ProvableStruct

/--
Initializes the BLAKE3 state vector from input variables.
This combines the chaining value with IV constants and counter/flags.
-/
def initializeStateVector (input_var : Var Inputs (F p)) : Var BLAKE3State (F p) :=
  let { chaining_value, block_words, counter_high, counter_low, block_len, flags } := input_var
  #v[
    chaining_value[0], chaining_value[1], chaining_value[2], chaining_value[3],
    chaining_value[4], chaining_value[5], chaining_value[6], chaining_value[7],
    const (U32.fromUInt32 iv[0]), const (U32.fromUInt32 iv[1]),
    const (U32.fromUInt32 iv[2]), const (U32.fromUInt32 iv[3]),
    counter_low, counter_high, block_len, flags
  ]

def main (input : Var Inputs (F p)) : Circuit (F p) (Var BLAKE3State (F p)) := do
  let state := initializeStateVector input
  -- Apply 7 rounds with message permutation between rounds (except the last)
  sevenRoundsApplyStyle ⟨state, input.block_words⟩

/-- Keep the large composed output behind an opaque name in parent proof types. -/
def applyRoundsOutput (input : Var Inputs (F p)) (i₀ : ℕ) : Var BLAKE3State (F p) :=
  sevenRoundsFinal.output
    ⟨initializeStateVector input, input.block_words⟩ i₀

@[circuit_norm] lemma sevenRoundsApplyStyle_assumptions (input : Round.Inputs (F p)) :
    sevenRoundsApplyStyle.Assumptions input = Round.Assumptions input := by
  rfl

@[circuit_norm] lemma sevenRoundsApplyStyle_spec
    (input : Round.Inputs (F p)) (state : BLAKE3State (F p)) :
    sevenRoundsApplyStyle.Spec input state = SevenRoundsSpec input state := by
  rfl

lemma applyRoundsOutput_eq (input : Var Inputs (F p)) (i₀ : ℕ) :
    applyRoundsOutput input i₀ = sevenRoundsApplyStyle.output
      ⟨initializeStateVector input, input.block_words⟩ i₀ := by
  rfl

-- TODO AUTOELAB the generated instance without here is not fully reduced, it contains
-- nested definitions like `sevenRoundsFinal` which we have to unfold in the soundness
-- proof, which makes the proof much more brittle and expensive. See https://github.com/Verified-zkEVM/clean/issues/394
-- that said -- full unfolding is also kind of bad for outputs here because it's a long chain of `Round.main ...`
-- that's why we override the output.
instance elaborated : ElaboratedCircuit (F p) Inputs BLAKE3State main := by
  elaborate_circuit_with {
    localLength _ := 5376
    output input i₀ := applyRoundsOutput input i₀
    channelsWithGuarantees := []
  } using by
    -- get rid of output with less unfolding
    simp +instances only [circuit_norm, applyRoundsOutput]
    -- localLength and channelsWithGuarantees need full unfolding down to `roundWithPermute` / `Round.circuit`
    simp +instances only [circuit_norm, sevenRoundsFinal, sixRoundsApplyStyle,
      sixRoundsWithPermute, fourRoundsWithPermute, twoRoundsWithPermute, roundWithPermute,
      Round.circuit]

def Assumptions (input : Inputs (F p)) :=
  let { chaining_value, block_words, counter_high, counter_low, block_len, flags } := input
  (∀ i : Fin 8, chaining_value[i].Normalized) ∧
  (∀ i : Fin 16, block_words[i].Normalized) ∧
  counter_high.Normalized ∧ counter_low.Normalized ∧ block_len.Normalized ∧ flags.Normalized

def Spec (input : Inputs (F p)) (out : BLAKE3State (F p)) :=
  let { chaining_value, block_words, counter_high, counter_low, block_len, flags } := input
  out.value = applyRounds
    (chaining_value.map U32.value)
    (block_words.map U32.value)
    (counter_low.value + 2^32 * counter_high.value)
    block_len.value
    flags.value ∧
  out.Normalized

-- Helper lemma that proves the initial state and messages are normalized
omit p_large_enough in
lemma initial_state_and_messages_are_normalized
    (env : Environment (F p))
    (input_var : Var Inputs (F p))
    (block_words : BLAKE3State (F p))
    (chaining_value counter_high counter_low block_len flags)
    (h_input : eval env input_var = { chaining_value, block_words, counter_high, counter_low, block_len, flags })
    (h_normalized : Assumptions { chaining_value, block_words, counter_high, counter_low, block_len, flags }) :
    (eval env (initializeStateVector input_var)).Normalized ∧ ∀ (i : Fin 16), block_words[i].Normalized := by
  obtain ⟨cv_var, bw_var, ch_var, cl_var, bl_var, fl_var⟩ := input_var
  set state_vec : BLAKE3State (Expression (F p)) := initializeStateVector
    ⟨cv_var, bw_var, ch_var, cl_var, bl_var, fl_var⟩
  simp only [Assumptions] at h_normalized
  simp only [circuit_norm] at *

  -- Helper to prove normalization of chaining value elements
  have h_chaining_value_normalized (i : ℕ) (h_i : i < 8) : (eval env (cv_var[i]'(by omega))).Normalized := by
    simp_all only [circuit_norm, eval_vector_eq_get]
    convert h_normalized.1 ⟨ i, h_i ⟩

  -- Show the state is normalized
  have h_state_normalized : BLAKE3State.Normalized (eval env state_vec) := by
    simp only [BLAKE3State.Normalized, state_vec, initializeStateVector, eval_vector]
    intro i
    fin_cases i
    -- First 8 elements are from chaining_value
    case «0» | «1» | «2» | «3» | «4» | «5» | «6» | «7» =>
      state_vec_norm_simp; simp [h_chaining_value_normalized]
    -- Next 4 are IV constants
    case «8» | «9» | «10» | «11» => state_vec_norm_simp_simple
    -- Last 4 are counter_low, counter_high, block_len, flags
    case «12» |«13» | «14» | «15» => state_vec_norm_simp_simple; simp_all

  constructor
  · apply h_state_normalized
  · -- Show the message is normalized
    intro i
    exact h_normalized.2.1 i

omit [Fact (Nat.Prime p)] p_large_enough in
private lemma counter_low_mod_eq (x : U32 (F p)) (h : x.Normalized) :
    x.value % 2^32 = x.value := by
  exact Nat.mod_eq_of_lt (U32.value_lt_of_normalized h)

omit [Fact (Nat.Prime p)] p_large_enough in
private lemma counter_high_div_eq (low high : U32 (F p)) (h : low.Normalized) :
    (low.value + 2^32 * high.value) / 2^32 = high.value := by
  rw [Nat.add_mul_div_left _ _ (by norm_num : 2^32 > 0)]
  have h_div : low.value / 2^32 = 0 :=
    Nat.div_eq_of_lt (U32.value_lt_of_normalized h)
  rw [h_div, zero_add]

omit [Fact (Nat.Prime p)] p_large_enough in
private def initialStateValues (input : Inputs (F p)) : Vector ℕ 16 := #v[
  (input.chaining_value.map U32.value)[0],
  (input.chaining_value.map U32.value)[1],
  (input.chaining_value.map U32.value)[2],
  (input.chaining_value.map U32.value)[3],
  (input.chaining_value.map U32.value)[4],
  (input.chaining_value.map U32.value)[5],
  (input.chaining_value.map U32.value)[6],
  (input.chaining_value.map U32.value)[7],
  iv[0].toNat, iv[1].toNat, iv[2].toNat, iv[3].toNat,
  input.counter_low.value, input.counter_high.value,
  input.block_len.value, input.flags.value
]

private lemma initializeStateVector_value_eq
    (env : Environment (F p)) (input_var : Var Inputs (F p)) (input : Inputs (F p))
    (h_input : eval env input_var = input) :
    (eval env (initializeStateVector input_var)).value = initialStateValues input := by
  rcases input_var with ⟨cv_var, bw_var, ch_var, cl_var, bl_var, fl_var⟩
  rcases input with ⟨chaining_value, block_words, counter_high,
    counter_low, block_len, flags⟩
  simp only [circuit_norm] at h_input
  simp only [BLAKE3State.value]
  rw [eval_vector]
  simp only [initialStateValues]
  simp only [initializeStateVector, Vector.map_mk,
    List.map_toArray, List.map_cons, List.map_nil]
  simp only [circuit_norm]
  simp only [getElem_eval_vector, h_input.1, h_input.2.2.1,
    h_input.2.2.2.1, h_input.2.2.2.2.1, h_input.2.2.2.2.2,
    U32.value_fromUInt32]

omit [Fact (Nat.Prime p)] p_large_enough in
private lemma applyRounds_eq_applySevenRounds_input
    (input : Inputs (F p)) (h_counter_low : input.counter_low.Normalized) :
    applyRounds
        (input.chaining_value.map U32.value)
        (input.block_words.map U32.value)
        (input.counter_low.value + 2^32 * input.counter_high.value)
        input.block_len.value
        input.flags.value =
      applySevenRounds (initialStateValues input) (input.block_words.map U32.value) := by
  rw [applyRounds_eq_applySevenRounds, Nat.add_mul_mod_self_left,
    counter_low_mod_eq input.counter_low h_counter_low,
    counter_high_div_eq input.counter_low input.counter_high h_counter_low]
  rfl

private lemma initialized_applySevenRounds_eq_applyRounds
    (env : Environment (F p)) (input_var : Var Inputs (F p)) (input : Inputs (F p))
    (h_input : eval env input_var = input) (h_counter_low : input.counter_low.Normalized) :
    applySevenRounds
        (eval env (initializeStateVector input_var)).value
        ((eval env input_var.block_words).map U32.value) =
      applyRounds
        (input.chaining_value.map U32.value)
        (input.block_words.map U32.value)
        (input.counter_low.value + 2^32 * input.counter_high.value)
        input.block_len.value
        input.flags.value := by
  have h_block_words : eval env input_var.block_words = input.block_words := by
    simpa only [circuit_norm] using congrArg Inputs.block_words h_input
  calc
    _ = applySevenRounds (initialStateValues input)
        (input.block_words.map U32.value) := congrArg₂ applySevenRounds
          (initializeStateVector_value_eq env input_var input h_input)
          (congrArg (Vector.map U32.value) h_block_words)
    _ = _ := (applyRounds_eq_applySevenRounds_input input h_counter_low).symm

theorem soundness : Soundness (F p) main Assumptions Spec := by
  circuit_proof_start_core
  rcases input_var with ⟨input_var_chaining_value, input_var_block_words,
    input_var_counter_high, input_var_counter_low, input_var_block_len, input_var_flags⟩
  rcases input with ⟨input_chaining_value, input_block_words,
    input_counter_high, input_counter_low, input_block_len, input_flags⟩
  simp +instances only [circuit_norm] at h_input
  dsimp only [Assumptions] at h_assumptions
  dsimp only [Spec]
  dsimp +instances only [elaborated]
  simp +instances only [main, circuit_norm] at h_holds ⊢
  let input_var_full : Var Inputs (F p) := ⟨input_var_chaining_value,
    input_var_block_words, input_var_counter_high, input_var_counter_low,
    input_var_block_len, input_var_flags⟩
  let input_full : Inputs (F p) := ⟨input_chaining_value, input_block_words,
    input_counter_high, input_counter_low, input_block_len, input_flags⟩
  have h_input_full : eval env input_var_full = input_full := by
    simp only [input_var_full, input_full, circuit_norm]
    exact h_input
  have h_initial_normalized := initial_state_and_messages_are_normalized
    (p := p) env input_var_full
    input_block_words input_chaining_value input_counter_high input_counter_low
    input_block_len input_flags h_input_full (by
      simp only [Assumptions]
      exact h_assumptions)
  have h_round_assumptions : Round.Assumptions
      {
        state := eval env (initializeStateVector input_var_full)
        message := eval env input_var_block_words
      } := by
    rw [h_input.2.1]
    exact h_initial_normalized
  have h_child_spec := h_holds h_round_assumptions
  simp only [SevenRoundsSpec] at h_child_spec
  have h_semantic := initialized_applySevenRounds_eq_applyRounds env
    input_var_full input_full h_input_full h_assumptions.2.2.2.1
  refine ⟨⟨?_, ?_⟩, Or.inr h_round_assumptions⟩
  · rw [applyRoundsOutput_eq]
    exact h_child_spec.1.trans h_semantic
  · rw [applyRoundsOutput_eq]
    exact h_child_spec.2

theorem completeness : Completeness (F p) main Assumptions := by
  circuit_proof_start

  -- Use the helper lemma to prove normalization
  apply initial_state_and_messages_are_normalized (p := p) env
    ⟨input_var_chaining_value, input_var_block_words, input_var_counter_high,
     input_var_counter_low, input_var_block_len, input_var_flags⟩
    input_block_words input_chaining_value input_counter_high input_counter_low
    input_block_len input_flags
  · simp only [circuit_norm]
    exact h_input
  · simp only [Assumptions]
    aesop

-- Unfortunately @[simps! (config := {isSimp := false, attrs := [`circuit_norm]})] timeouts.
-- Therefore I had to add simplification rules `circuit_assumptions_is` and `circuit_spec_is` manually.
def circuit : FormalCircuit (F p) Inputs BLAKE3State := {
  main, elaborated, Assumptions, Spec, soundness, completeness
}

end Gadgets.BLAKE3.ApplyRounds
