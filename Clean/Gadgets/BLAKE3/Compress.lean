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

instance elaborated : ElaboratedCircuit (F p) ApplyRounds.Inputs BLAKE3State where
  main
  localLength input := ApplyRounds.circuit.localLength input + FinalStateUpdate.circuit.localLength ⟨default, input.chaining_value⟩
  output := fun input offset =>
    let applyRounds_out := ApplyRounds.circuit.output input offset
    FinalStateUpdate.circuit.output
      ⟨applyRounds_out, input.chaining_value⟩
      (offset + ApplyRounds.circuit.localLength input)
  output_eq := by
    intro input offset
    simp only [main, Circuit.bind_def, Circuit.output, circuit_norm]
  localAdds_eq := by simp only [circuit_norm, main]

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

theorem soundness : Soundness (F p) elaborated Assumptions Spec := by
  circuit_proof_start
  simp_all only [circuit_norm, ApplyRounds.circuit,
    ApplyRounds.Spec, FinalStateUpdate.circuit, FinalStateUpdate.Assumptions, compress,
    ApplyRounds.Assumptions, FinalStateUpdate.Spec]

lemma ApplyRounds.circuit_assumptions_is :
  ApplyRounds.circuit.Assumptions (F := F p) = ApplyRounds.Assumptions := rfl

lemma ApplyRouunds.circuit_spec_is :
  ApplyRounds.circuit.Spec (F := F p) = ApplyRounds.Spec := rfl

theorem completeness : Completeness (F p) elaborated Assumptions := by
  circuit_proof_start
  simp_all only [circuit_norm, ApplyRounds.circuit_assumptions_is, ApplyRouunds.circuit_spec_is,
    ApplyRounds.Spec, FinalStateUpdate.circuit, FinalStateUpdate.Assumptions,
    ApplyRounds.Assumptions, FinalStateUpdate.Spec]

def circuit : FormalCircuit (F p) ApplyRounds.Inputs BLAKE3State := {
  elaborated with Assumptions, Spec, soundness, completeness
}

end Gadgets.BLAKE3.Compress
