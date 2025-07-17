import Clean.Gadgets.BLAKE3.BLAKE3State

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

def Spec (state : BLAKE3State (F p)) (out: BLAKE3State (F p)) :=
  out.value = permute state.value ∧ out.Normalized

theorem soundness : Soundness (F p) elaborated Assumptions Spec := by
  intro i0 env state_var state h_input h_normalized h_holds
  simp only [Spec, BLAKE3State.value, Vector.map, ElaboratedCircuit.output, ↓Fin.getElem_fin,
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
    simp only [Assumptions, BLAKE3State.Normalized] at h_normalized
    fin_cases i <;> simp only [msgPermutation, h_normalized]

theorem completeness : Completeness (F p) elaborated Assumptions := by
  rintro i0 env state_var henv state h_inputs h_normalized
  simp_all only [Circuit.operations, ElaboratedCircuit.main, main, pure, ↓Fin.getElem_fin,
    Environment.UsesLocalWitnessesCompleteness.eq_1, Circuit.ConstraintsHold.Completeness.eq_1]

@[simps! (config := {isSimp := false, attrs := [`circuit_norm]})]
def circuit : FormalCircuit (F p) BLAKE3State BLAKE3State :=
  { elaborated with Assumptions, Spec, soundness, completeness }

end Gadgets.BLAKE3.Permute
