import Clean.Gadgets.BLAKE3.BLAKE3State
import Clean.Gadgets.BLAKE3.BLAKE3G
import Clean.Specs.BLAKE3
import Clean.Circuit.Provable

namespace Gadgets.BLAKE3.Round
variable {p : ℕ} [Fact p.Prime] [p_large_enough: Fact (p > 2^16 + 2^8)]
instance : Fact (p > 512) := .mk (by linarith [p_large_enough.elim])

open Specs.BLAKE3 (round roundConstants)

structure Inputs (F : Type) where
  state : BLAKE3State F
  message : Vector (U32 F) 16

instance : ProvableStruct Inputs where
  components := [BLAKE3State, ProvableVector U32 16]
  toComponents := fun { state, message } => .cons state (.cons message .nil)
  fromComponents := fun (.cons state (.cons message .nil)) => { state, message }

def main (input : Var Inputs (F p)) : Circuit (F p) (Var BLAKE3State (F p)) := do
  let { state, message } := input
  let state ← subcircuit (G.circuit 0 4 8 12) ⟨state, message[0], message[1]⟩
  let state ← subcircuit (G.circuit 1 5 9 13) ⟨state, message[2], message[3]⟩
  let state ← subcircuit (G.circuit 2 6 10 14) ⟨state, message[4], message[5]⟩
  let state ← subcircuit (G.circuit 3 7 11 15) ⟨state, message[6], message[7]⟩
  let state ← subcircuit (G.circuit 0 5 10 15) ⟨state, message[8], message[9]⟩
  let state ← subcircuit (G.circuit 1 6 11 12) ⟨state, message[10], message[11]⟩
  let state ← subcircuit (G.circuit 2 7 8 13) ⟨state, message[12], message[13]⟩
  let state ← subcircuit (G.circuit 3 4 9 14) ⟨state, message[14], message[15]⟩
  return state

-- #eval! main (p:=pBabybear) default |>.localLength
-- #eval! main (p:=pBabybear) default |>.output
instance elaborated : ElaboratedCircuit (F p) Inputs BLAKE3State where
  main := main
  localLength _ := 768
  localLength_eq input i0 := by
    simp only [main, circuit_norm, G.circuit, subcircuit_norm, G.elaborated]

def Assumptions (input : Inputs (F p)) :=
  let { state, message } := input
  state.Normalized ∧ (∀ i : Fin 16, message[i].Normalized)

def Spec (input : Inputs (F p)) (out: BLAKE3State (F p)) :=
  let { state, message } := input
  out.value = round state.value (message.map U32.value) ∧ out.Normalized

theorem soundness : Soundness (F p) elaborated Assumptions Spec := by
  intro i0 env ⟨state_var, message_var⟩ ⟨state, message⟩ h_input h_normalized h_holds
  simp only [circuit_norm, Inputs.mk.injEq] at h_input

  dsimp [Assumptions] at h_normalized
  obtain ⟨h_state, h_message⟩ := h_normalized
  obtain ⟨h_eval_state, h_eval_message⟩ := h_input

  dsimp [circuit_norm, subcircuit_norm, main, G.elaborated, G.circuit, Rotation32.output] at h_holds
  simp [h_eval_state, h_eval_message, G.Spec, circuit_norm, getElem_eval_vector, G.Assumptions] at h_holds
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8⟩ := h_holds
  simp_all only [forall_const]

  specialize c1 (h_message 0) (h_message 1)
  rw [c1.left] at c2
  specialize c2 c1.right (h_message 2) (h_message 3)
  rw [c2.left] at c3
  specialize c3 c2.right (h_message 4) (h_message 5)
  rw [c3.left] at c4
  specialize c4 c3.right (h_message 6) (h_message 7)
  rw [c4.left] at c5
  specialize c5 c4.right (h_message 8) (h_message 9)
  rw [c5.left] at c6
  specialize c6 c5.right (h_message 10) (h_message 11)
  rw [c6.left] at c7
  specialize c7 c6.right (h_message 12) (h_message 13)
  rw [c7.left] at c8
  specialize c8 c7.right (h_message 14) (h_message 15)

  clear c1 c2 c3 c4 c5 c6 c7

  simp [Spec, circuit_norm, main, subcircuit_norm, elaborated, G.elaborated, G.circuit,
    Specs.BLAKE3.round, Vector.foldl, roundConstants, circuit_norm]
  constructor
  · rw [←c8.left]; rfl
  · exact c8.right

theorem completeness : Completeness (F p) elaborated Assumptions := by
  rintro i0 env input_var henv input h_input h_normalized
  sorry

def circuit : FormalCircuit (F p) Inputs BLAKE3State := {
  elaborated with Assumptions, Spec, soundness, completeness
}

end Gadgets.BLAKE3.Round
