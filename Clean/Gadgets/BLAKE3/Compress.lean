import Clean.Gadgets.BLAKE3.ApplyRounds
import Clean.Gadgets.BLAKE3.FinalStateUpdate
import Clean.Specs.BLAKE3
import Clean.Circuit.Provable
import Clean.Utils.Tactics

namespace Gadgets.BLAKE3.Compress
variable {p : ℕ} [Fact p.Prime] [p_large_enough: Fact (p > 2^16 + 2^8)]
instance : Fact (p > 512) := .mk (by linarith [p_large_enough.elim])

open Specs.BLAKE3 (compress)

/--
Main circuit that chains ApplyRounds and FinalStateUpdate.
-/
def main (input : Var ApplyRounds.Inputs (F p)) : Circuit (F p) (Var BLAKE3State (F p)) := do
  -- First apply the 7 rounds
  let state ← ApplyRounds.circuit input
  -- Then apply final state update
  FinalStateUpdate.circuit ⟨state, input.chaining_value⟩

instance elaborated : ElaboratedCircuit (F p) ApplyRounds.Inputs BLAKE3State main := by
  elaborate_circuit

def Assumptions (input : ApplyRounds.Inputs (F p)) : Prop :=
  ApplyRounds.Assumptions input

def Spec (input : ApplyRounds.Inputs (F p)) (output : BLAKE3State (F p)) : Prop :=
  let { chaining_value, block_words, counter_high, counter_low, block_len, flags } := input
  output.value = compress
    (chaining_value.map U32.value)
    (block_words.map U32.value)
    (counter_low.value + 2^32 * counter_high.value)
    block_len.value
    flags.value ∧
  output.Normalized

theorem soundness : Soundness (F p) main Assumptions Spec := by
  circuit_proof_all [circuit_norm, ApplyRounds.circuit,
    ApplyRounds.Spec, FinalStateUpdate.circuit, FinalStateUpdate.Assumptions, compress,
    ApplyRounds.Assumptions, FinalStateUpdate.Spec]

theorem completeness : Completeness (F p) main Assumptions := by
  circuit_proof_all [ApplyRounds.circuit,
    ApplyRounds.Spec, FinalStateUpdate.circuit, FinalStateUpdate.Assumptions,
    ApplyRounds.Assumptions, FinalStateUpdate.Spec]

set_option maxRecDepth 8192 in
def circuit : FormalCircuit (F p) ApplyRounds.Inputs BLAKE3State := {
  main, Assumptions, Spec, soundness, completeness
  computableWitnesses := by
    intro n input env env'
    have eA : ∀ v, (ApplyRounds.circuit (p:=p)).localLength v = 5376 := fun _ => rfl
    have eF : ∀ v, (FinalStateUpdate.circuit (p:=p)).localLength v = 64 := fun _ => rfl
    simp only [circuit_norm, main, eA, eF]
    refine ⟨⟨fun h => ?_, fun h => ?_⟩, fun h h_agrees => ?_⟩
    · exact FormalCircuit.toSubcircuit_computableWitnesses _
        (by first | exact h | (simp only [circuit_norm]; exact h))
    · refine FormalCircuit.toSubcircuit_computableWitnesses_onlyAccessedBelow_of_offset_eq _
        (by first | omega | (simp only [eA, eF]; try omega)) fun h_agrees => ?_
      have oAR := FormalCircuit.output_of_input_eq (ApplyRounds.circuit (p:=p)) (n := n)
        (by first | exact h | (simp only [circuit_norm]; exact h))
        (ProverEnvironment.agreesBelow_of_le h_agrees (by simp only [eA]; omega))
      simp only [circuit_norm]
      first
        | exact oAR
        | exact ⟨oAR, congrArg (fun s : ApplyRounds.Inputs (F p) => s.chaining_value) h⟩
    · have oAR := FormalCircuit.output_of_input_eq (ApplyRounds.circuit (p:=p)) (n := n)
        (by first | exact h | (simp only [circuit_norm]; exact h))
        (ProverEnvironment.agreesBelow_of_le h_agrees (by simp only [eA]; omega))
      have oF := FormalCircuit.output_of_input_eq (FinalStateUpdate.circuit (p:=p))
        (input_var := ⟨(ApplyRounds.circuit (p:=p)).output input n, input.chaining_value⟩)
        (n := n + 5376)
        (by simp only [circuit_norm]
            first
              | exact oAR
              | exact ⟨oAR, congrArg (fun s : ApplyRounds.Inputs (F p) => s.chaining_value) h⟩)
        (ProverEnvironment.agreesBelow_of_le h_agrees (by simp only [eA, eF]; omega))
      simp only [circuit_norm]
      (try and_intros) <;> first | grind | exact oF
}

end Gadgets.BLAKE3.Compress
