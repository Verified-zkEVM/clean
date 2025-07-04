import Clean.Gadgets.BLAKE3.BLAKE3State
import Clean.Gadgets.BLAKE3.Round
import Clean.Gadgets.BLAKE3.Permute
import Clean.Types.U32
import Clean.Circuit.Provable
import Clean.Specs.BLAKE3

namespace Gadgets.BLAKE3.ApplyRounds
variable {p : ℕ} [Fact p.Prime] [p_large_enough: Fact (p > 2^16 + 2^8)]
instance : Fact (p > 512) := .mk (by linarith [p_large_enough.elim])

open Specs.BLAKE3 (applyRounds iv)

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
