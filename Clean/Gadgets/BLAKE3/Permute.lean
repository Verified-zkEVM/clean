import Clean.Gadgets.BLAKE3.BLAKE3State
import Clean.Circuit

namespace Gadgets.BLAKE3.Permute
variable {p : ℕ} [Fact p.Prime]

open Specs.BLAKE3 (msgPermutation permute)

def main (state : Var BLAKE3State (F p)) : Circuit (F p) (Var BLAKE3State (F p)) := do
  return Vector.ofFn (fun i => state[msgPermutation[i]])

instance elaborated: ElaboratedCircuit (F p) BLAKE3State BLAKE3State where
  main := main
  localLength _ := 0
  output state i0 := Vector.ofFn (fun i => state[msgPermutation[i]])

def Assumptions (state : BLAKE3State (F p)) := state.Normalized

def Spec (state : BLAKE3State (F p)) (out : BLAKE3State (F p)) :=
  out.value = permute state.value ∧ out.Normalized

theorem soundness : Soundness (F p) elaborated Assumptions Spec := by
  circuit_proof_start
  simp only [BLAKE3State.value, Vector.map, ↓Fin.getElem_fin,
    eval_vector, Vector.toArray_ofFn, Array.map_map, permute, Vector.getElem_mk, Array.getElem_map,
    ↓Vector.getElem_toArray, Vector.mk_eq]
  constructor
  · ext i hi
    · simp only [Array.size_map, Array.size_ofFn]
    simp only [Array.getElem_map, Array.getElem_ofFn]
    rw [Function.comp_apply, getElem_eval_vector, h_input]
  · simp [BLAKE3State.Normalized]
    intro i
    rw [getElem_eval_vector, h_input]
    simp only [BLAKE3State.Normalized] at h_assumptions
    fin_cases i <;> simp only [msgPermutation, h_assumptions]

theorem completeness : Completeness (F p) elaborated Assumptions := by
  circuit_proof_all

def circuit : FormalCircuit (F p) BLAKE3State BLAKE3State :=
  { elaborated with Assumptions, Spec, soundness, completeness }

end Gadgets.BLAKE3.Permute
