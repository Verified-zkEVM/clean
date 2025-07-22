import Clean.Gadgets.BLAKE3.BLAKE3State
import Clean.Gadgets.BLAKE3.BLAKE3G
import Clean.Specs.BLAKE3
import Clean.Circuit.Provable

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

def main (input : Var Inputs (F p)) : Circuit (F p) (Var BLAKE3State (F p)) := do
  let { state, message } := input
  -- TODO: refactor using a for loop
  let state ← G.circuit 0 4 8 12 ⟨state, message[0], message[1]⟩
  let state ← G.circuit 1 5 9 13 ⟨state, message[2], message[3]⟩
  let state ← G.circuit 2 6 10 14 ⟨state, message[4], message[5]⟩
  let state ← G.circuit 3 7 11 15 ⟨state, message[6], message[7]⟩
  let state ← G.circuit 0 5 10 15 ⟨state, message[8], message[9]⟩
  let state ← G.circuit 1 6 11 12 ⟨state, message[10], message[11]⟩
  let state ← G.circuit 2 7 8 13 ⟨state, message[12], message[13]⟩
  let state ← G.circuit 3 4 9 14 ⟨state, message[14], message[15]⟩
  return state

-- #eval! main (p:=pBabybear) default |>.localLength
-- #eval! main (p:=pBabybear) default |>.output
instance elaborated : ElaboratedCircuit (F p) Inputs BLAKE3State where
  main := main
  localLength _ := 768
  localLength_eq input i0 := by
    simp only [main, circuit_norm, G.circuit, G.elaborated]

def Assumptions (input : Inputs (F p)) :=
  let { state, message } := input
  state.Normalized ∧ (∀ i : Fin 16, message[i].Normalized)

def Spec (input : Inputs (F p)) (out: BLAKE3State (F p)) :=
  let { state, message } := input
  out.rawValue = round state.rawValue (message.map U32.rawValueU32) ∧ out.Normalized

theorem soundness : Soundness (F p) elaborated Assumptions Spec := by
  intro i0 env ⟨state_var, message_var⟩ ⟨state, message⟩ h_input h_normalized h_holds
  simp only [circuit_norm, Inputs.mk.injEq] at h_input

  dsimp only [Assumptions, Fin.getElem_fin] at h_normalized
  obtain ⟨h_state, h_message⟩ := h_normalized
  obtain ⟨h_eval_state, h_eval_message⟩ := h_input

  dsimp only [ElaboratedCircuit.main, main, Fin.isValue, G.circuit, G.elaborated, Fin.val_zero,
    Fin.coe_ofNat_eq_mod, Nat.reduceMod, Rotation32.output, Fin.reduceMod, Nat.cast_ofNat,
    Fin.val_one, Fin.val_two, pure, Circuit.bind_def, subcircuit.eq_1, ElaboratedCircuit.output,
    FormalCircuit.toSubcircuit.eq_1, Circuit.operations, ElaboratedCircuit.localLength,
    List.cons_append, List.nil_append, Operations.localLength.eq_5, Operations.localLength.eq_1,
    Nat.add_zero, Circuit.ConstraintsHold.Soundness.eq_5,
    Circuit.ConstraintsHold.Soundness.eq_1] at h_holds
  simp only [G.Assumptions, ↓ProvableStruct.eval_eq_eval, ProvableStruct.eval, fromComponents,
    ProvableStruct.eval.go, h_eval_state, getElem_eval_vector, h_eval_message, G.Spec, Fin.isValue,
    Nat.cast_zero, and_imp, and_true] at h_holds
  -- something.value appears here instead of soething.rawValue, why?
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8⟩ := h_holds
  simp_all only [forall_const]

  -- resolve chain of assumptions
  specialize c1 (h_message 0) (h_message 1)
  rw [c1.left] at c2
  specialize c2 c1.right (h_message 2) (h_message 3)
  rw [c2.left] at c3
  specialize c3 c2.right (h_message 4) (h_message 5)
  rw [c3.left] at c4
  specialize c4 c3.right (h_message 6) (h_message 7)
  rw [c4.left] at c5
  specialize c5 c4.right (h_message 8) (h_message 9)
  rw [c5.left] at c6
  specialize c6 c5.right (h_message 10) (h_message 11)
  rw [c6.left] at c7
  specialize c7 c6.right (h_message 12) (h_message 13)
  rw [c7.left] at c8
  specialize c8 c7.right (h_message 14) (h_message 15)

  clear c1 c2 c3 c4 c5 c6 c7

  -- now c8 is basically the goal
  simp only [Spec, ElaboratedCircuit.output, Circuit.output, main, G.circuit, G.elaborated,
    Fin.isValue, Fin.val_zero, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Fin.val_one, Fin.val_two,
    Nat.mod_succ, pure, Circuit.bind_def, subcircuit, FormalCircuit.toSubcircuit,
    Circuit.operations, ElaboratedCircuit.main, ElaboratedCircuit.localLength, List.append_nil,
    Operations.localLength.eq_5, Operations.localLength, add_zero, id_eq, subcircuit.eq_1,
    FormalCircuit.toSubcircuit.eq_1, Operations.localLength.eq_1, Nat.add_zero, List.cons_append,
    List.nil_append, Circuit.localLength, Operations.SubcircuitsConsistent.eq_1, Specs.BLAKE3.round,
    Vector.foldl, roundConstants, ↓Fin.getElem_fin, ↓Vector.getElem_map, List.size_toArray,
    List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, List.foldl_toArray',
    List.foldl_cons, List.foldl_nil]
  constructor
  ·

/- c8.1 RHS
    Specs.BLAKE3.g
      (Specs.BLAKE3.g
        (Specs.BLAKE3.g
          (Specs.BLAKE3.g
            (Specs.BLAKE3.g
              (Specs.BLAKE3.g
                (Specs.BLAKE3.g (Specs.BLAKE3.g state.rawValue 0 4 8 12 ↑message[0].value ↑message[1].value) 1 5 9 13
                  ↑message[2].value ↑message[3].value)
                2 6 10 14 ↑message[4].value ↑message[5].value)
              3 7 11 15 ↑message[6].value ↑message[7].value)
            0 5 10 15 ↑message[8].value ↑message[9].value)
          1 6 11 12 ↑message[10].value ↑message[11].value)
        2 7 8 13 ↑message[12].value ↑message[13].value)
      3 4 9 14 ↑message[14].value ↑message[15].value -/

    rw [←c8.left]; rfl
  · exact c8.right

theorem completeness : Completeness (F p) elaborated Assumptions := by
  rintro i0 env ⟨state_var, message_var⟩ henv ⟨state, message⟩ h_input h_normalized

  simp only [main, circuit_norm, G.circuit, G.Assumptions, G.Spec] at ⊢ henv h_input
  simp only [↓ProvableStruct.eval_eq_eval, ProvableStruct.eval, fromComponents,
    ProvableStruct.eval.go, Inputs.mk.injEq, Environment.UsesLocalWitnessesCompleteness,
    getElem_eval_vector, Fin.isValue, and_imp, and_true] at h_input henv ⊢

  rw [h_input.left, h_input.right] at henv
  simp [Assumptions] at h_normalized
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8⟩ := henv

  specialize c1 h_normalized.left (h_normalized.right 0) (h_normalized.right 1)
  specialize c2 c1.right (h_normalized.right 2) (h_normalized.right 3)
  specialize c3 c2.right (h_normalized.right 4) (h_normalized.right 5)
  specialize c4 c3.right (h_normalized.right 6) (h_normalized.right 7)
  specialize c5 c4.right (h_normalized.right 8) (h_normalized.right 9)
  specialize c6 c5.right (h_normalized.right 10) (h_normalized.right 11)
  specialize c7 c6.right (h_normalized.right 12) (h_normalized.right 13)
  specialize c8 c7.right (h_normalized.right 14) (h_normalized.right 15)

  simp only [Fin.isValue, c1.right, true_and, c2.right, c3.right, c4.right, c5.right, c6.right,
    c7.right]
  clear c1 c2 c3 c4 c5 c6 c7 c8

  rw [h_input.left]
  simp only [Fin.forall_fin_succ, Fin.isValue, Fin.val_zero, Fin.val_succ, zero_add, Nat.reduceAdd,
    Fin.val_eq_zero, IsEmpty.forall_iff, and_true] at h_normalized

  simp only [h_normalized, getElem_eval_vector, h_input.right, and_self]

def circuit : FormalCircuit (F p) Inputs BLAKE3State := {
  elaborated with Assumptions, Spec, soundness, completeness
}

end Gadgets.BLAKE3.Round
