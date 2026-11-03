module

public import Clean.Gadgets.BLAKE3.BLAKE3State
public import Clean.Circuit

@[expose] public section

namespace Gadgets.BLAKE3.Permute
variable {p : ℕ} [Fact p.Prime]

open Specs.BLAKE3 (msgPermutation permute)

def main (state : Var BLAKE3State (F p)) : Circuit (F p) (Var BLAKE3State (F p)) := do
  return Vector.ofFn (fun i => state[msgPermutation[i]])

@[reducible] instance elaborated: ElaboratedCircuit (F p) BLAKE3State BLAKE3State main := by
  elaborate_circuit

def Assumptions (state : BLAKE3State (F p)) := state.Normalized

def Spec (state : BLAKE3State (F p)) (out : BLAKE3State (F p)) :=
  out.value = permute state.value ∧ out.Normalized

theorem soundness : Soundness (F p) main Assumptions Spec := by
  circuit_proof_start
  constructor
  · ext i hi
    simp only [BLAKE3State.value, permute, Vector.getElem_map, Vector.getElem_ofFn, Fin.getElem_fin]
  · intro i
    simp only [Vector.getElem_ofFn]
    exact h_assumptions _

theorem completeness : Completeness (F p) main Assumptions := by
  circuit_proof_all

def circuit : FormalCircuit (F p) BLAKE3State BLAKE3State :=
  { main, elaborated, Assumptions, Spec, soundness, completeness }

end Gadgets.BLAKE3.Permute
