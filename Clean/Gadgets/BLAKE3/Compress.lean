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
def main {sentences : PropertySet (F p)} (order : SentenceOrder sentences) (input : Var ApplyRounds.Inputs (F p)) : Circuit sentences (Var BLAKE3State (F p)) := do
  -- First apply the 7 rounds
  let state ← ApplyRounds.circuit order input
  -- Then apply final state update
  FinalStateUpdate.circuit order ⟨state, input.chaining_value⟩

def elaborated {sentences : PropertySet (F p)} (order : SentenceOrder sentences) : ElaboratedCircuit (F p) sentences ApplyRounds.Inputs BLAKE3State where
  main := main order
  localLength input := (ApplyRounds.circuit order).localLength input + (FinalStateUpdate.circuit order).localLength ⟨default, input.chaining_value⟩
  output := fun input offset =>
    let applyRounds_out := (ApplyRounds.circuit order).output input offset
    (FinalStateUpdate.circuit order).output
      ⟨applyRounds_out, input.chaining_value⟩
      (offset + (ApplyRounds.circuit order).localLength input)
  yields _ _ _ := ∅
  output_eq := by
    intro input offset
    simp only [main, Circuit.bind_def, Circuit.output, circuit_norm]
  yields_eq := by
    intro env input offset
    simp only [main, circuit_norm, ElaboratedCircuit.yields_eq]
    simp [ApplyRounds.circuit, FinalStateUpdate.circuit, ApplyRounds.elaborated, FinalStateUpdate.elaborated]

def Assumptions (input : ApplyRounds.Inputs (F p)) : Prop :=
  ApplyRounds.Assumptions input

def CompletenessAssumptions {sentences : PropertySet (F p)} (_ : YieldContext sentences) (input : ApplyRounds.Inputs (F p)) : Prop :=
  Assumptions input

def Spec {sentences : PropertySet (F p)} (_checked : CheckedYields sentences) (input : ApplyRounds.Inputs (F p)) (output : BLAKE3State (F p)) : Prop :=
  let { chaining_value, block_words, counter_high, counter_low, block_len, flags } := input
  output.value = compress
    (chaining_value.map U32.value)
    (block_words.map U32.value)
    (counter_low.value + 2^32 * counter_high.value)
    block_len.value
    flags.value ∧
  output.Normalized

theorem soundness {sentences : PropertySet (F p)} (order : SentenceOrder sentences) : Soundness (F p) (elaborated order) order Assumptions Spec := by
  circuit_proof_start [elaborated]

  simp_all only [circuit_norm, ApplyRounds.circuit,
    ApplyRounds.Spec, FinalStateUpdate.circuit, FinalStateUpdate.Assumptions, compress,
    ApplyRounds.Assumptions, FinalStateUpdate.Spec]

lemma ApplyRounds.circuit_assumptions_is {sentences : PropertySet (F p)} (order : SentenceOrder sentences) :
  (ApplyRounds.circuit order).Assumptions = ApplyRounds.Assumptions := rfl

lemma ApplyRouunds.circuit_spec_is {sentences : PropertySet (F p)} (order : SentenceOrder sentences) :
  (ApplyRounds.circuit order).Spec = ApplyRounds.Spec := rfl

theorem completeness {sentences : PropertySet (F p)} (order : SentenceOrder sentences) : Completeness (F p) sentences (elaborated order) CompletenessAssumptions := by
  circuit_proof_start [elaborated, CompletenessAssumptions, Assumptions, ApplyRounds.Assumptions]
  simp_all only [circuit_norm, CompletenessAssumptions, Assumptions,
    ApplyRounds.circuit, ApplyRounds.CompletenessAssumptions,
    ApplyRouunds.circuit_spec_is,
    ApplyRounds.Spec, FinalStateUpdate.circuit, FinalStateUpdate.Assumptions, FinalStateUpdate.CompletenessAssumptions,
    FinalStateUpdate.Spec, ApplyRounds.Assumptions]

def circuit {sentences : PropertySet (F p)} (order : SentenceOrder sentences) : FormalCircuit order ApplyRounds.Inputs BLAKE3State := {
  elaborated := elaborated order
  Assumptions
  CompletenessAssumptions
  completenessAssumptions_implies_assumptions := fun _ _ h => h
  Spec
  soundness := soundness order
  completeness := completeness order
}

end Gadgets.BLAKE3.Compress
