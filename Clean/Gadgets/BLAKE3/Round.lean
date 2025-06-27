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
  .foldl (_const_out := by
    rintro ⟨inputs, a, b, c, d, i, j, h_j⟩
    intro i0
    simp [circuit_norm, G.circuit]
    --TODO: this is not trivial because the output depends on a b c d.
    -- however, the `roundConstants` are fixed, so morally they are constants
    sorry
  ) roundConstants state
    fun state (a, b, c, d, i, j) => subcircuit (G.circuit a b c d) ⟨state, message[i], message[j]⟩

-- #eval! main (p:=p_babybear) default |>.local_length
-- #eval! main (p:=p_babybear) default |>.output
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

  simp [circuit_norm, subcircuit_norm, main, G.elaborated, G.circuit] at h_holds

  sorry

theorem completeness : Completeness (F p) elaborated Assumptions := by
  rintro i0 env input_var henv input h_input h_normalized
  sorry

def circuit : FormalCircuit (F p) Inputs BLAKE3State := {
  elaborated with Assumptions, Spec, soundness, completeness
}

end Gadgets.BLAKE3.Round
