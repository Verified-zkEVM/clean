module

public import Clean.Circuit
public import Clean.Specs.Poseidon

@[expose] public section

namespace Circomlib.Poseidon.Sigma

open Specs.Poseidon (F)

/-- The Poseidon S-box circuit, computing `x ^ 5` with three witnesses. -/
def main (input : Expression F) : Circuit F (Expression F) := do
  let in2 <== input * input
  let in4 <== in2 * in2
  let out <== in4 * input
  return out

def circuit : FormalCircuit F field field where
  main := main

  Assumptions _ := True
  Spec (input : F) (output : F) := output = input ^ 5

  soundness := by
    intro offset env input_var input h_input h_assumptions h_constraints
    simp only [circuit_norm, main] at *
    obtain ⟨h_in2, h_in4, h_out⟩ := h_constraints
    rw [h_input] at *
    rw [h_out, h_in4, h_in2]
    ring

  completeness := by
    simp_all only [circuit_norm, main]

end Circomlib.Poseidon.Sigma
