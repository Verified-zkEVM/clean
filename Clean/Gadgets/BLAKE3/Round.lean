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
  let state ← subcircuit (G.circuit 0 4 8 12) ⟨state, message[0], message[1]⟩
  let state ← subcircuit (G.circuit 1 5 9 13) ⟨state, message[2], message[3]⟩
  let state ← subcircuit (G.circuit 2 6 10 14) ⟨state, message[4], message[5]⟩
  let state ← subcircuit (G.circuit 3 7 11 15) ⟨state, message[6], message[7]⟩
  let state ← subcircuit (G.circuit 0 5 10 15) ⟨state, message[8], message[9]⟩
  let state ← subcircuit (G.circuit 1 6 11 12) ⟨state, message[10], message[11]⟩
  let state ← subcircuit (G.circuit 2 7 8 13) ⟨state, message[12], message[13]⟩
  let state ← subcircuit (G.circuit 3 4 9 14) ⟨state, message[14], message[15]⟩

  -- TODO: this last copy is unnecessary, however if it not copied
  -- the output is a mess to deal with in subsequent circuits
  let state <== state
  return state

-- #eval! main (p:=pBabybear) default |>.localLength
-- #eval! main (p:=pBabybear) default |>.output
instance elaborated : ElaboratedCircuit (F p) Inputs BLAKE3State where
  main := main
  localLength _ := 832
  localLength_eq input i0 := by
    simp only [main, circuit_norm, G.circuit, subcircuit_norm, G.elaborated]

  output input i0 := varFromOffset BLAKE3State (i0 + 768)
  output_eq := by
    intros
    dsimp [main, circuit_norm, G.circuit]

  subcircuitsConsistent := by
    intros
    dsimp only [main, Fin.isValue, G.circuit, HasAssignEq.assign_eq, HasAssertEq.assert_eq,
      assertEquals, Circuit.pure_def, Circuit.bind_def, assertion.eq_1, List.cons_append,
      List.nil_append, ProvableType.witness.eq_1, size, Nat.reduceMul, Operations.localLength.eq_2,
      Operations.localLength.eq_1, Nat.add_zero, subcircuit.eq_1, ElaboratedCircuit.output,
      Fin.coe_ofNat_eq_mod, Nat.reduceMod, Operations.localLength.eq_5,
      Circuit.subcircuit_localLength_eq, ElaboratedCircuit.localLength, Fin.val_two, Fin.val_one,
      Fin.val_zero, Circuit.operations, Operations.SubcircuitsConsistent.eq_1,
      Operations.forAll.eq_5, Operations.forAll.eq_2, Circuit.assertion_localLength_eq,
      ↓Equality.elaborated_eq, Operations.forAll.eq_1]
    simp only [and_true, true_and]
    (repeat' constructor) <;> ac_rfl



def Assumptions (input : Inputs (F p)) :=
  let { state, message } := input
  state.Normalized ∧ (∀ i : Fin 16, message[i].Normalized)

def Spec (input : Inputs (F p)) (out: BLAKE3State (F p)) :=
  let { state, message } := input
  out.value = round state.value (message.map U32.value) ∧ out.Normalized

theorem soundness : Soundness (F p) elaborated Assumptions Spec := by
  intro i0 env ⟨state_var, message_var⟩ ⟨state, message⟩ h_input h_normalized h_holds
  simp only [circuit_norm, Inputs.mk.injEq] at h_input

  dsimp only [Assumptions, Fin.getElem_fin] at h_normalized
  obtain ⟨h_state, h_message⟩ := h_normalized
  obtain ⟨h_eval_state, h_eval_message⟩ := h_input

  dsimp only [ElaboratedCircuit.main, main, Fin.isValue, G.circuit, G.elaborated,
    Fin.coe_ofNat_eq_mod, Nat.reduceMod, Rotation32.output, Fin.reduceMod, Nat.cast_ofNat,
    HasAssignEq.assign_eq, HasAssertEq.assert_eq, assertEquals, Circuit.pure_def, Circuit.bind_def,
    assertion.eq_1, FormalAssertion.toSubcircuit.eq_1, ↓Equality.elaborated_eq, Circuit.operations,
    ElaboratedCircuit.localLength, Environment.ExtendsVector.eq_1, List.cons_append,
    List.nil_append, ProvableType.witness.eq_1, size, Nat.reduceMul, Operations.localLength.eq_2,
    Operations.localLength.eq_1, Nat.add_zero, subcircuit.eq_1, ElaboratedCircuit.output,
    FormalCircuit.toSubcircuit.eq_1, Operations.localLength.eq_5,
    Circuit.ConstraintsHold.Soundness.eq_5, Circuit.ConstraintsHold.Soundness.eq_2,
    Circuit.ConstraintsHold.Soundness.eq_1] at h_holds
  simp only [G.Assumptions, ↓ProvableStruct.eval_eq_eval, ProvableStruct.eval, fromComponents,
    ProvableStruct.eval.go, h_eval_state, getElem_eval_vector, h_eval_message, G.Spec, Fin.isValue,
    Nat.cast_zero, and_imp, Equality.circuit, forall_const, and_true] at h_holds
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9⟩ := h_holds
  simp_all only [forall_const]

  -- resolve chain of assumptions
  specialize c1 (h_message 0) (h_message 1)
  rw [c1.left] at c2
  specialize c2 c1.right (h_message 2) (h_message 3)
  clear c1

  rw [c2.left] at c3
  specialize c3 c2.right (h_message 4) (h_message 5)
  clear c2

  rw [c3.left] at c4
  specialize c4 c3.right (h_message 6) (h_message 7)
  clear c3

  rw [c4.left] at c5
  specialize c5 c4.right (h_message 8) (h_message 9)
  clear c4

  rw [c5.left] at c6
  specialize c6 c5.right (h_message 10) (h_message 11)
  clear c5

  rw [c6.left] at c7
  specialize c7 c6.right (h_message 12) (h_message 13)
  clear c6

  rw [c7.left] at c8
  specialize c8 c7.right (h_message 14) (h_message 15)
  clear c7

  -- TODO for some reason `circuit_norm` dos not apply automatically this thm
  rw [eval_pair (α := BLAKE3State) (β := BLAKE3State) env] at c9
  simp [circuit_norm] at c9

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
  · rw [c9, c8.left]
  · rw [c9]
    exact c8.right

theorem completeness : Completeness (F p) elaborated Assumptions := by
  rintro i0 env ⟨state_var, message_var⟩ henv ⟨state, message⟩ h_input h_normalized

  dsimp only [elaborated, main, Fin.isValue, G.circuit, Circuit.pure_def, Circuit.bind_def,
    subcircuit.eq_1, ElaboratedCircuit.output, Fin.coe_ofNat_eq_mod, Nat.reduceMod,
    FormalCircuit.toSubcircuit.eq_1, ElaboratedCircuit.main, Circuit.operations, G.Assumptions,
    G.Spec, ElaboratedCircuit.localLength, List.cons_append, List.nil_append, Fin.val_two,
    Operations.localLength.eq_5, Operations.localLength.eq_1, Nat.add_zero, Fin.val_one,
    Fin.val_zero, Circuit.output, Circuit.ConstraintsHold.Completeness.eq_5,
    Circuit.ConstraintsHold.Completeness.eq_1] at ⊢ henv h_input
  simp only [↓ProvableStruct.eval_eq_eval, ProvableStruct.eval, fromComponents,
    ProvableStruct.eval.go, Inputs.mk.injEq, Environment.UsesLocalWitnessesCompleteness,
    getElem_eval_vector, Fin.isValue, and_imp, and_true] at h_input henv ⊢

  rw [h_input.left, h_input.right] at henv
  simp [Assumptions] at h_normalized
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9⟩ := henv


  specialize c1 h_normalized.left (h_normalized.right 0) (h_normalized.right 1)
  specialize c2 c1.right (h_normalized.right 2) (h_normalized.right 3)
  specialize c3 c2.right (h_normalized.right 4) (h_normalized.right 5)
  specialize c4 c3.right (h_normalized.right 6) (h_normalized.right 7)
  specialize c5 c4.right (h_normalized.right 8) (h_normalized.right 9)
  specialize c6 c5.right (h_normalized.right 10) (h_normalized.right 11)
  specialize c7 c6.right (h_normalized.right 12) (h_normalized.right 13)
  specialize c8 c7.right (h_normalized.right 14) (h_normalized.right 15)
  sorry
  -- simp only [Fin.isValue, c1.right, true_and, c2.right, c3.right, c4.right, c5.right, c6.right,
  --   c7.right]
  -- clear c1 c2 c3 c4 c5 c6 c7 c8

  -- rw [h_input.left]
  -- simp only [Fin.forall_fin_succ, Fin.isValue, Fin.val_zero, Fin.val_succ, zero_add, Nat.reduceAdd,
  --   Fin.val_eq_zero, IsEmpty.forall_iff, and_true] at h_normalized

  -- simp only [h_normalized, getElem_eval_vector, h_input.right, and_self]

def circuit : FormalCircuit (F p) Inputs BLAKE3State := {
  elaborated with Assumptions, Spec, soundness, completeness
}

end Gadgets.BLAKE3.Round
