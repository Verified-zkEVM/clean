import Clean.Utils.Tactics
import Clean.Circuit

namespace TestCircuitProofStartNames

open ProvenZK Circuit

-- Test that circuit_proof_start preserves standard names

example {F : Type} [Field F] {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    (circuit : ElaboratedCircuit F Input Output) 
    (Assumptions : Input F → Prop)
    (Spec : Input F → Output F → Prop) :
    Soundness F circuit Assumptions Spec := by
  circuit_proof_start
  -- At this point we should have: offset, env, input_var, input, h_input, h_normalized, h_holds
  -- Check that these names exist by using them
  have : ℕ := offset
  have : Environment F := env  
  have : Input (Expression F) := input_var
  have : Input F := input
  have : eval env input_var = input := h_input
  have : Assumptions input := h_normalized
  have : ConstraintsHold.Soundness env (circuit.main input_var offset).2 := h_holds
  sorry

example {F : Type} [Field F] {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    (circuit : ElaboratedCircuit F Input Output) 
    (Assumptions : Input F → Prop) :
    Completeness F circuit Assumptions := by
  circuit_proof_start
  -- At this point we should have: offset, env, input_var, henv
  -- Note: provable_struct_simp eliminates input and h_input by substituting eval env input_var
  -- Check that these names exist by using them
  have : ℕ := offset
  have : Environment F := env
  have : Input (Expression F) := input_var
  have : env.UsesLocalWitnessesCompleteness offset (circuit.main input_var offset).2 := henv
  -- After provable_struct_simp, we work with eval env input_var instead of input
  sorry

end TestCircuitProofStartNames