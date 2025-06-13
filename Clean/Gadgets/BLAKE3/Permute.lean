import Clean.Gadgets.Xor.Xor32
import Clean.Gadgets.BLAKE3.BLAKE3State
import Clean.Gadgets.Addition32.Addition32
import Clean.Gadgets.Rotation32.Rotation32
import Clean.Specs.BLAKE3
import Clean.Circuit.Provable

namespace Gadgets.BLAKE3.G
variable {p : ℕ} [Fact p.Prime]

open Specs.BLAKE3 (msgPermutation permute)

def main (state : Var BLAKE3State (F p)) : Circuit (F p) (Var BLAKE3State (F p)) := do
  return Vector.ofFn (fun i => state[msgPermutation[i]])

-- #eval! main (p:=p_babybear) default |>.operations.local_length
-- #eval! main (p:=p_babybear) default |>.output
instance elaborated: ElaboratedCircuit (F p) BLAKE3State BLAKE3State where
  main := main
  local_length _ := 0
  output state i0 := Vector.ofFn (fun i => state[msgPermutation[i]])

def assumptions (state : BLAKE3State (F p)) := state.is_normalized

def spec (state : BLAKE3State (F p)) (out: BLAKE3State (F p)) :=
  out.value = permute state.value ∧ out.is_normalized

theorem soundness : Soundness (F p) elaborated assumptions spec := by
  intro i0 env state_var state h_input h_normalized h_holds
  simp only [spec, BLAKE3State.value, Vector.map, ElaboratedCircuit.output, ↓Fin.getElem_fin,
    eval_vector, Vector.toArray_ofFn, Array.map_map, permute, Vector.getElem_mk, Array.getElem_map,
    ↓Vector.getElem_toArray, Vector.mk_eq]
  constructor
  · ext i hi
    · simp only [Array.size_map, Array.size_ofFn]
    simp only [Array.getElem_map, Array.getElem_ofFn]
    rw [Function.comp_apply, getElem_eval_vector, h_input]
  · simp [BLAKE3State.is_normalized]
    intro i
    rw [getElem_eval_vector, h_input]
    simp only [assumptions, BLAKE3State.is_normalized] at h_normalized
    fin_cases i <;> simp only [msgPermutation, h_normalized]

theorem completeness : Completeness (F p) elaborated assumptions := by
  rintro i0 env state_var henv state h_inputs h_normalized
  simp_all only [Circuit.operations, ElaboratedCircuit.main, main, pure, ↓Fin.getElem_fin,
    Environment.uses_local_witnesses_completeness.eq_1, Circuit.constraints_hold.completeness.eq_1]

def circuit : FormalCircuit (F p) BLAKE3State BLAKE3State := {
  elaborated with assumptions, spec, soundness, completeness
}

end Gadgets.BLAKE3.G
