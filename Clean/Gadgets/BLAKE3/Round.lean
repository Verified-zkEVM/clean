import Clean.Gadgets.BLAKE3.BLAKE3State
import Clean.Gadgets.BLAKE3.BLAKE3G
import Clean.Specs.BLAKE3
import Clean.Circuit.Provable
import Clean.Utils.Tactics

namespace Gadgets.BLAKE3.Round
variable {p : ℕ} [Fact p.Prime] [p_large_enough: Fact (p > 2^16 + 2^8)]
instance : Fact (p > 512) := .mk (by linarith [p_large_enough.elim])

open Specs.BLAKE3 (round roundConstants)

structure Inputs (F : Type) where
  state : BLAKE3State F
  message : Vector (U32 F) 16

instance : ProvableStruct Inputs where
  components := [BLAKE3State, ProvableVector U32 16]
  toComponents := fun { state, message } => .cons state (.cons message .nil)
  fromComponents := fun (.cons state (.cons message .nil)) => { state, message }

def main {sentences : PropertySet (F p)} (order : SentenceOrder sentences) (input : Var Inputs (F p)) : Circuit sentences (Var BLAKE3State (F p)) := do
  let { state, message } := input
  -- TODO: refactor using a for loop
  let state ← G.circuit order 0 4 8 12 ⟨state, message[0], message[1]⟩
  let state ← G.circuit order 1 5 9 13 ⟨state, message[2], message[3]⟩
  let state ← G.circuit order 2 6 10 14 ⟨state, message[4], message[5]⟩
  let state ← G.circuit order 3 7 11 15 ⟨state, message[6], message[7]⟩
  let state ← G.circuit order 0 5 10 15 ⟨state, message[8], message[9]⟩
  let state ← G.circuit order 1 6 11 12 ⟨state, message[10], message[11]⟩
  let state ← G.circuit order 2 7 8 13 ⟨state, message[12], message[13]⟩
  let state ← G.circuit order 3 4 9 14 ⟨state, message[14], message[15]⟩
  return state

-- #eval! main (p:=pBabybear) default |>.localLength
-- #eval! main (p:=pBabybear) default |>.output
def elaborated {sentences : PropertySet (F p)} (order : SentenceOrder sentences) : ElaboratedCircuit (F p) sentences Inputs BLAKE3State where
  main := main order
  localLength _ := 768
  localLength_eq input i0 := by
    simp only [main, circuit_norm, G.circuit, G.elaborated]
  yields _ _ _ := ∅
  yields_eq := by
    intros _ _ _
    simp only [main, circuit_norm, ElaboratedCircuit.yields_eq]
    simp [G.circuit, G.elaborated]

def Assumptions (input : Inputs (F p)) :=
  let { state, message } := input
  state.Normalized ∧ (∀ i : Fin 16, message[i].Normalized)

def CompletenessAssumptions {sentences : PropertySet (F p)} (_ : YieldContext sentences) (input : Inputs (F p)) :=
  Assumptions input

def Spec {sentences : PropertySet (F p)} (_checked : CheckedYields sentences) (input : Inputs (F p)) (out : BLAKE3State (F p)) :=
  let { state, message } := input
  out.value = round state.value (message.map U32.value) ∧ out.Normalized

theorem soundness {sentences : PropertySet (F p)} (order : SentenceOrder sentences) : Soundness (F p) (elaborated order) order Assumptions Spec := by
  circuit_proof_start [elaborated]

  obtain ⟨h_state, h_message⟩ := h_assumptions

  dsimp only [ElaboratedCircuit.main, main, Fin.isValue, G.circuit, G.elaborated, Fin.val_zero,
    Fin.coe_ofNat_eq_mod, Nat.reduceMod, Rotation32.output, Fin.reduceMod, Nat.cast_ofNat,
    Fin.val_one, Fin.val_two, pure, Circuit.bind_def, subcircuit.eq_1, ElaboratedCircuit.output,
    FormalCircuit.toSubcircuit.eq_1, Circuit.operations, ElaboratedCircuit.localLength,
    List.cons_append, List.nil_append, Operations.localLength.eq_5, Operations.localLength.eq_1,
    Nat.add_zero, Circuit.ConstraintsHold.Soundness.eq_5,
    Circuit.ConstraintsHold.Soundness.eq_1] at h_holds
  simp only [G.Assumptions, h_input, getElem_eval_vector, G.Spec, Fin.isValue, and_imp] at h_holds

  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8⟩ := h_holds
  simp_all only [forall_const]

  -- resolve chain of assumptions
  specialize c1 (h_message 0) (h_message 1)
  rw [c1.2.1] at c2
  specialize c2 c1.2.2 (h_message 2) (h_message 3)
  rw [c2.2.1] at c3
  specialize c3 c2.2.2 (h_message 4) (h_message 5)
  rw [c3.2.1] at c4
  specialize c4 c3.2.2 (h_message 6) (h_message 7)
  rw [c4.2.1] at c5
  specialize c5 c4.2.2 (h_message 8) (h_message 9)
  rw [c5.2.1] at c6
  specialize c6 c5.2.2 (h_message 10) (h_message 11)
  rw [c6.2.1] at c7
  specialize c7 c6.2.2 (h_message 12) (h_message 13)
  rw [c7.2.1] at c8
  specialize c8 c7.2.2 (h_message 14) (h_message 15)

  clear c1 c2 c3 c4 c5 c6 c7

  -- now c8 is basically the goal
  simp only [ElaboratedCircuit.output, G.circuit, G.elaborated,
    Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.reduceMod,
    Nat.mod_succ, ElaboratedCircuit.localLength, Specs.BLAKE3.round,
    Vector.foldl, roundConstants, ↓Fin.getElem_fin, ↓Vector.getElem_map, List.size_toArray,
    List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, List.foldl_toArray',
    List.foldl_cons, List.foldl_nil]
  constructor
  · rw [←c8.2.1]; rfl
  · exact c8.2.2

theorem completeness {sentences : PropertySet (F p)} (order : SentenceOrder sentences) : Completeness (F p) sentences (elaborated order) CompletenessAssumptions := by
  circuit_proof_start [elaborated, G.circuit, G.elaborated, G.Assumptions, G.CompletenessAssumptions, G.Spec, Environment.UsesLocalWitnessesAndYieldsCompleteness,
    getElem_eval_vector, Fin.isValue, and_imp, and_true, Assumptions]

  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8⟩ := h_env

  specialize c1 h_assumptions.left (h_assumptions.right 0) (h_assumptions.right 1)
  specialize c2 c1.2.2 (h_assumptions.right 2) (h_assumptions.right 3)
  specialize c3 c2.2.2 (h_assumptions.right 4) (h_assumptions.right 5)
  specialize c4 c3.2.2 (h_assumptions.right 6) (h_assumptions.right 7)
  specialize c5 c4.2.2 (h_assumptions.right 8) (h_assumptions.right 9)
  specialize c6 c5.2.2 (h_assumptions.right 10) (h_assumptions.right 11)
  specialize c7 c6.2.2 (h_assumptions.right 12) (h_assumptions.right 13)
  specialize c8 c7.2.2 (h_assumptions.right 14) (h_assumptions.right 15)

  simp only [Fin.isValue, c1.2.2, true_and, c2.2.2, c3.2.2, c4.2.2, c5.2.2, c6.2.2,
    c7.2.2]
  clear c1 c2 c3 c4 c5 c6 c7 c8

  simp only [Fin.forall_fin_succ, Fin.isValue, Fin.val_zero, Fin.val_succ, zero_add, Nat.reduceAdd,
    Fin.val_eq_zero, IsEmpty.forall_iff, and_true] at h_assumptions

  simp only [h_assumptions, and_self]

def circuit {sentences : PropertySet (F p)} (order : SentenceOrder sentences) : FormalCircuit order Inputs BLAKE3State := {
  elaborated := elaborated order
  Assumptions
  CompletenessAssumptions
  completenessAssumptions_implies_assumptions := fun _ _ h => h
  Spec
  soundness := soundness order
  completeness := completeness order
}

end Gadgets.BLAKE3.Round
