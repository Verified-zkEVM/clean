import Clean.Gadgets.BLAKE3.ApplyRounds
import Clean.Gadgets.BLAKE3.FinalStateUpdate
import Clean.Specs.BLAKE3
import Clean.Circuit.Provable

namespace Gadgets.BLAKE3.Compress
variable {p : ℕ} [Fact p.Prime] [p_large_enough: Fact (p > 2^16 + 2^8)]
instance : Fact (p > 512) := .mk (by linarith [p_large_enough.elim])

open Specs.BLAKE3 (compress)

/--
Main circuit that chains ApplyRounds and FinalStateUpdate.
-/
def main (input : Var ApplyRounds.Inputs (F p)) : Circuit (F p) (Var BLAKE3State (F p)) := do
  -- First apply the 7 rounds
  let state ← subcircuit ApplyRounds.circuit input
  -- Then apply final state update
  subcircuit FinalStateUpdate.circuit ⟨state, input.chaining_value⟩

instance elaborated : ElaboratedCircuit (F p) ApplyRounds.Inputs BLAKE3State where
  main := main
  localLength input := ApplyRounds.circuit.localLength input + FinalStateUpdate.circuit.localLength ⟨default, input.chaining_value⟩
  localLength_eq := by
    intro input offset
    simp only [main, Circuit.bind_def, Circuit.localLength, circuit_norm]
    rfl
  output := fun input offset =>
    let applyRounds_out := ApplyRounds.circuit.output input offset
    FinalStateUpdate.circuit.output 
      ⟨applyRounds_out, input.chaining_value⟩ 
      (offset + ApplyRounds.circuit.localLength input)
  output_eq := by
    intro input offset
    simp only [main, Circuit.bind_def, Circuit.output, circuit_norm]
  subcircuitsConsistent := by
    intro input offset
    simp only [main, Circuit.bind_def, Circuit.operations, circuit_norm]
    ring

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
  sorry

theorem completeness : Completeness (F p) elaborated Assumptions := by
  sorry

def circuit : FormalCircuit (F p) ApplyRounds.Inputs BLAKE3State := {
  elaborated with Assumptions, Spec, soundness, completeness
}

end Gadgets.BLAKE3.Compress