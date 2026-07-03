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

def circuit : FormalCircuit (F p) ApplyRounds.Inputs BLAKE3State := {
  main, Assumptions, Spec, soundness, completeness
}

end Gadgets.BLAKE3.Compress
