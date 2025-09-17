import Clean.Gadgets.BLAKE3.BLAKE3State

namespace Gadgets.BLAKE3.Permute
variable {p : ℕ} [Fact p.Prime]

open Specs.BLAKE3 (msgPermutation permute)

def main {sentences : PropertySet (F p)} (_order : SentenceOrder sentences) (state : Var BLAKE3State (F p)) : Circuit sentences (Var BLAKE3State (F p)) := do
  return Vector.ofFn (fun i => state[msgPermutation[i]])

instance elaborated {sentences : PropertySet (F p)} (order : SentenceOrder sentences) : ElaboratedCircuit (F p) sentences BLAKE3State BLAKE3State where
  main := main order
  localLength _ := 0
  output state i0 := Vector.ofFn (fun i => state[msgPermutation[i]])

def Assumptions (state : BLAKE3State (F p)) := state.Normalized

def Spec {sentences : PropertySet (F p)} (_checked : CheckedYields sentences) (state : BLAKE3State (F p)) (out : BLAKE3State (F p)) :=
  out.value = permute state.value ∧ out.Normalized

theorem soundness {sentences : PropertySet (F p)} {order : SentenceOrder sentences} : Soundness (F p) (elaborated order) order Assumptions Spec := by
  intro i0 env state_var checked state_input state h_input h_assumptions h_holds
  constructor
  · -- Prove yielded sentences hold (nothing is yielded)
    intro s
    simp [Operations.localYields, circuit_norm, main]
  · -- Prove the spec
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
      simp only [Assumptions, BLAKE3State.Normalized] at h_assumptions
      fin_cases i <;> simp only [msgPermutation, h_assumptions]

def CompletenessAssumptions {sentences : PropertySet (F p)} (_ : YieldContext sentences) (state : BLAKE3State (F p)) :=
  Assumptions state

theorem completeness {sentences : PropertySet (F p)} {order : SentenceOrder sentences} : Completeness (F p) sentences (elaborated order) CompletenessAssumptions := by
  rintro i0 env state_var henv state h_inputs h_normalized
  simp_all only [Circuit.operations, ElaboratedCircuit.main, main, pure, ↓Fin.getElem_fin,
    Environment.UsesLocalWitnessesAndYieldsCompleteness.eq_1, Circuit.ConstraintsHold.Completeness.eq_1]
  intro _
  trivial

def circuit {sentences : PropertySet (F p)} (order : SentenceOrder sentences) : FormalCircuit order BLAKE3State BLAKE3State :=
  { elaborated order with
    Assumptions
    CompletenessAssumptions
    Spec
    soundness
    completeness
    completenessAssumptions_implies_assumptions := fun _ _ h => h
  }

end Gadgets.BLAKE3.Permute
