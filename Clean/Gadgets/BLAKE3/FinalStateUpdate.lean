import Clean.Gadgets.Xor.Xor32
import Clean.Gadgets.BLAKE3.BLAKE3State
import Clean.Specs.BLAKE3
import Clean.Circuit.Provable
import Clean.Utils.Tactics

namespace Gadgets.BLAKE3.FinalStateUpdate
variable {p : ℕ} [Fact p.Prime] [p_large_enough: Fact (p > 2^16 + 2^8)]
instance : Fact (p > 512) := .mk (by linarith [p_large_enough.elim])

open Specs.BLAKE3 (finalStateUpdate)

structure Inputs (F : Type) where
  state : BLAKE3State F
  chaining_value : Vector (U32 F) 8
deriving ProvableStruct

def main (input : Var Inputs (F p)) : Circuit (F p) (Var BLAKE3State (F p)) := do
  let { state, chaining_value } := input

  -- XOR first 8 words with last 8 words
  let s0 ← Xor32.circuit ⟨state[0], state[8]⟩
  let s1 ← Xor32.circuit ⟨state[1], state[9]⟩
  let s2 ← Xor32.circuit ⟨state[2], state[10]⟩
  let s3 ← Xor32.circuit ⟨state[3], state[11]⟩
  let s4 ← Xor32.circuit ⟨state[4], state[12]⟩
  let s5 ← Xor32.circuit ⟨state[5], state[13]⟩
  let s6 ← Xor32.circuit ⟨state[6], state[14]⟩
  let s7 ← Xor32.circuit ⟨state[7], state[15]⟩

  -- XOR last 8 words with chaining value
  let s8 ← Xor32.circuit ⟨chaining_value[0], state[8]⟩
  let s9 ← Xor32.circuit ⟨chaining_value[1], state[9]⟩
  let s10 ← Xor32.circuit ⟨chaining_value[2], state[10]⟩
  let s11 ← Xor32.circuit ⟨chaining_value[3], state[11]⟩
  let s12 ← Xor32.circuit ⟨chaining_value[4], state[12]⟩
  let s13 ← Xor32.circuit ⟨chaining_value[5], state[13]⟩
  let s14 ← Xor32.circuit ⟨chaining_value[6], state[14]⟩
  let s15 ← Xor32.circuit ⟨chaining_value[7], state[15]⟩

  return #v[s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15]

-- #eval main (p:=p_babybear) default |>.local_length
-- #eval main (p:=p_babybear) default |>.output
instance elaborated : ElaboratedCircuit (F p) Inputs BLAKE3State where
  main := main
  localLength _ := 64
  output inputs i0 := #v[
    varFromOffset U32 (i0 + 0),
    varFromOffset U32 (i0 + 4),
    varFromOffset U32 (i0 + 8),
    varFromOffset U32 (i0 + 12),
    varFromOffset U32 (i0 + 16),
    varFromOffset U32 (i0 + 20),
    varFromOffset U32 (i0 + 24),
    varFromOffset U32 (i0 + 28),
    varFromOffset U32 (i0 + 32),
    varFromOffset U32 (i0 + 36),
    varFromOffset U32 (i0 + 40),
    varFromOffset U32 (i0 + 44),
    varFromOffset U32 (i0 + 48),
    varFromOffset U32 (i0 + 52),
    varFromOffset U32 (i0 + 56),
    varFromOffset U32 (i0 + 60)
  ]

  localLength_eq _ n := by
    dsimp only [main, circuit_norm, Xor32.circuit, Xor32.elaborated]
  localAdds_eq _ _ _ := by
    simp only [main, circuit_norm, Operations.localAdds]

def Assumptions (input : Inputs (F p)) :=
  let { state, chaining_value } := input
  state.Normalized ∧ (∀ i : Fin 8, chaining_value[i].Normalized)

def Spec (input : Inputs (F p)) (out : BLAKE3State (F p)) :=
  let { state, chaining_value } := input
  out.value = finalStateUpdate state.value (chaining_value.map U32.value) ∧ out.Normalized

theorem soundness : Soundness (F p) elaborated Assumptions Spec := by
  intro i0 env ⟨state_var, chaining_value_var⟩ ⟨state, chaining_value⟩ h_input h_normalized h_holds
  simp only [circuit_norm, Inputs.mk.injEq] at h_input

  dsimp only [main, circuit_norm, Xor32.circuit, Xor32.elaborated] at h_holds
  simp only [FormalCircuit.toSubcircuit, Circuit.operations, ElaboratedCircuit.main,
    ElaboratedCircuit.localLength, Xor32.Assumptions,
    ProvableStruct.eval_eq_eval, ProvableStruct.eval, fromComponents, components, toComponents,
    ProvableStruct.eval.go, getElem_eval_vector, h_input, Xor32.Spec, ElaboratedCircuit.output,
    and_imp, Nat.add_zero, add_zero, and_true] at h_holds

  ring_nf at h_holds

  simp only [Assumptions, BLAKE3State.Normalized] at h_normalized
  obtain ⟨state_norm, chaining_value_norm⟩ := h_normalized

  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15⟩ := h_holds
  specialize c0 (state_norm 0) (state_norm 8)
  specialize c1 (state_norm 1) (state_norm 9)
  specialize c2 (state_norm 2) (state_norm 10)
  specialize c3 (state_norm 3) (state_norm 11)
  specialize c4 (state_norm 4) (state_norm 12)
  specialize c5 (state_norm 5) (state_norm 13)
  specialize c6 (state_norm 6) (state_norm 14)
  specialize c7 (state_norm 7) (state_norm 15)
  specialize c8 (chaining_value_norm 0) (state_norm 8)
  specialize c9 (chaining_value_norm 1) (state_norm 9)
  specialize c10 (chaining_value_norm 2) (state_norm 10)
  specialize c11 (chaining_value_norm 3) (state_norm 11)
  specialize c12 (chaining_value_norm 4) (state_norm 12)
  specialize c13 (chaining_value_norm 5) (state_norm 13)
  specialize c14 (chaining_value_norm 6) (state_norm 14)
  specialize c15 (chaining_value_norm 7) (state_norm 15)

  simp [Spec, circuit_norm, eval_vector, BLAKE3State.value, BLAKE3State.Normalized, finalStateUpdate]
  ring_nf
  simp only [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, and_self,
    true_and]

  simp only [Fin.forall_fin_succ, Fin.isValue, Fin.val_zero, List.getElem_cons_zero, c0,
    Fin.val_succ, List.getElem_cons_succ, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13,
    c14, Fin.val_eq_zero, zero_add, c15, implies_true, and_self]

theorem completeness : Completeness (F p) elaborated Assumptions := by
  circuit_proof_start [BLAKE3State.Normalized]

  obtain ⟨h_input_state, h_input_cv⟩ := h_input
  obtain ⟨state_norm, chaining_value_norm⟩ := h_assumptions

  dsimp only [main, circuit_norm, Xor32.circuit, Xor32.elaborated] at h_env ⊢
  simp only [h_input_state, h_input_cv, circuit_norm, and_imp,
    Xor32.Assumptions, Xor32.Spec, getElem_eval_vector] at h_env ⊢

  -- Prove all normalization facts from the universal hypotheses
  refine ⟨⟨state_norm 0, state_norm 8⟩, ⟨state_norm 1, state_norm 9⟩,
    ⟨state_norm 2, state_norm 10⟩, ⟨state_norm 3, state_norm 11⟩,
    ⟨state_norm 4, state_norm 12⟩, ⟨state_norm 5, state_norm 13⟩,
    ⟨state_norm 6, state_norm 14⟩, ⟨state_norm 7, state_norm 15⟩,
    ⟨chaining_value_norm 0, state_norm 8⟩, ⟨chaining_value_norm 1, state_norm 9⟩,
    ⟨chaining_value_norm 2, state_norm 10⟩, ⟨chaining_value_norm 3, state_norm 11⟩,
    ⟨chaining_value_norm 4, state_norm 12⟩, ⟨chaining_value_norm 5, state_norm 13⟩,
    ⟨chaining_value_norm 6, state_norm 14⟩, chaining_value_norm 7, state_norm 15⟩

def circuit : FormalCircuit (F p) Inputs BLAKE3State := {
  elaborated with Assumptions, Spec, soundness, completeness
}

end Gadgets.BLAKE3.FinalStateUpdate
