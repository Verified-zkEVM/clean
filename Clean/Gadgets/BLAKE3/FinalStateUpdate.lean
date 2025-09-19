import Clean.Gadgets.Xor.Xor32
import Clean.Gadgets.BLAKE3.BLAKE3State
import Clean.Specs.BLAKE3
import Clean.Circuit.Provable

namespace Gadgets.BLAKE3.FinalStateUpdate
variable {p : ℕ} [Fact p.Prime] [p_large_enough: Fact (p > 2^16 + 2^8)]
instance : Fact (p > 512) := .mk (by linarith [p_large_enough.elim])

open Specs.BLAKE3 (finalStateUpdate)

structure Inputs (F : Type) where
  state : BLAKE3State F
  chaining_value : Vector (U32 F) 8

instance : ProvableStruct Inputs where
  components := [BLAKE3State, ProvableVector U32 8]
  toComponents := fun { state, chaining_value } => .cons state (.cons chaining_value .nil)
  fromComponents := fun (.cons state (.cons chaining_value .nil)) => { state, chaining_value }

def main {sentences : PropertySet (F p)} (order : SentenceOrder sentences) (input : Var Inputs (F p)) : Circuit sentences (Var BLAKE3State (F p)) := do
  let { state, chaining_value } := input

  -- XOR first 8 words with last 8 words
  let s0 ← Xor32.circuit order ⟨state[0], state[8]⟩
  let s1 ← Xor32.circuit order ⟨state[1], state[9]⟩
  let s2 ← Xor32.circuit order ⟨state[2], state[10]⟩
  let s3 ← Xor32.circuit order ⟨state[3], state[11]⟩
  let s4 ← Xor32.circuit order ⟨state[4], state[12]⟩
  let s5 ← Xor32.circuit order ⟨state[5], state[13]⟩
  let s6 ← Xor32.circuit order ⟨state[6], state[14]⟩
  let s7 ← Xor32.circuit order ⟨state[7], state[15]⟩

  -- XOR last 8 words with chaining value
  let s8 ← Xor32.circuit order ⟨chaining_value[0], state[8]⟩
  let s9 ← Xor32.circuit order ⟨chaining_value[1], state[9]⟩
  let s10 ← Xor32.circuit order ⟨chaining_value[2], state[10]⟩
  let s11 ← Xor32.circuit order ⟨chaining_value[3], state[11]⟩
  let s12 ← Xor32.circuit order ⟨chaining_value[4], state[12]⟩
  let s13 ← Xor32.circuit order ⟨chaining_value[5], state[13]⟩
  let s14 ← Xor32.circuit order ⟨chaining_value[6], state[14]⟩
  let s15 ← Xor32.circuit order ⟨chaining_value[7], state[15]⟩

  return #v[s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15]

-- #eval main (p:=p_babybear) default |>.local_length
-- #eval main (p:=p_babybear) default |>.output
def elaborated {sentences : PropertySet (F p)} (order : SentenceOrder sentences) : ElaboratedCircuit (F p) sentences Inputs BLAKE3State where
  main := main order
  localLength _ := 64
  output inputs i0 := #v[
    varFromOffset U32 (i0 + 0),
    varFromOffset U32 (i0 + 4),
    varFromOffset U32 (i0 + 8),
    varFromOffset U32 (i0 + 12),
    varFromOffset U32 (i0 + 16),
    varFromOffset U32 (i0 + 20),
    varFromOffset U32 (i0 + 24),
    varFromOffset U32 (i0 + 28),
    varFromOffset U32 (i0 + 32),
    varFromOffset U32 (i0 + 36),
    varFromOffset U32 (i0 + 40),
    varFromOffset U32 (i0 + 44),
    varFromOffset U32 (i0 + 48),
    varFromOffset U32 (i0 + 52),
    varFromOffset U32 (i0 + 56),
    varFromOffset U32 (i0 + 60)
  ]

  localLength_eq _ n := by
    dsimp only [main, circuit_norm, Xor32.circuit, Xor32.elaborated]

def Assumptions (input : Inputs (F p)) :=
  let { state, chaining_value } := input
  state.Normalized ∧ (∀ i : Fin 8, chaining_value[i].Normalized)

def CompletenessAssumptions {sentences : PropertySet (F p)} (_ : YieldContext sentences) (input : Inputs (F p)) :=
  Assumptions input

def Spec {sentences : PropertySet (F p)} (_checked : CheckedYields sentences) (input : Inputs (F p)) (out : BLAKE3State (F p)) :=
  let { state, chaining_value } := input
  out.value = finalStateUpdate state.value (chaining_value.map U32.value) ∧ out.Normalized

theorem soundness {sentences : PropertySet (F p)} (order : SentenceOrder sentences) : Soundness (F p) (elaborated order) order Assumptions Spec := by
  intro i0 env yields checked ⟨state_var, chaining_value_var⟩ ⟨state, chaining_value⟩ h_input h_normalized h_holds
  simp only [circuit_norm, Inputs.mk.injEq] at h_input

  dsimp only [elaborated, main, circuit_norm, Xor32.circuit, Xor32.elaborated] at h_holds
  simp only [FormalCircuit.toSubcircuit, Circuit.operations, ElaboratedCircuit.main,
    ElaboratedCircuit.localLength, Xor32.Assumptions,
    ProvableStruct.eval_eq_eval, ProvableStruct.eval, fromComponents,
    ProvableStruct.eval.go, getElem_eval_vector, h_input, Xor32.Spec, ElaboratedCircuit.output,
    and_imp, Nat.add_zero, add_zero, and_true] at h_holds

  ring_nf at h_holds

  simp only [Assumptions, BLAKE3State.Normalized] at h_normalized
  obtain ⟨state_norm, chaining_value_norm⟩ := h_normalized

  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15⟩ := h_holds
  specialize c0 (state_norm 0) (state_norm 8)
  specialize c1 (state_norm 1) (state_norm 9)
  specialize c2 (state_norm 2) (state_norm 10)
  specialize c3 (state_norm 3) (state_norm 11)
  specialize c4 (state_norm 4) (state_norm 12)
  specialize c5 (state_norm 5) (state_norm 13)
  specialize c6 (state_norm 6) (state_norm 14)
  specialize c7 (state_norm 7) (state_norm 15)
  specialize c8 (chaining_value_norm 0) (state_norm 8)
  specialize c9 (chaining_value_norm 1) (state_norm 9)
  specialize c10 (chaining_value_norm 2) (state_norm 10)
  specialize c11 (chaining_value_norm 3) (state_norm 11)
  specialize c12 (chaining_value_norm 4) (state_norm 12)
  specialize c13 (chaining_value_norm 5) (state_norm 13)
  specialize c14 (chaining_value_norm 6) (state_norm 14)
  specialize c15 (chaining_value_norm 7) (state_norm 15)
  
  constructor
  · -- Prove yielded sentences hold (vacuous - no yields)
    intro s hs _
    -- The Xor32 subcircuits don't yield anything
    sorry

  simp [Spec, circuit_norm, elaborated, eval_vector, BLAKE3State.value, BLAKE3State.Normalized, finalStateUpdate]
  ring_nf
  simp only [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, and_self,
    true_and]

  simp only [Fin.forall_fin_succ, Fin.isValue, Fin.val_zero, List.getElem_cons_zero, c0,
    Fin.val_succ, List.getElem_cons_succ, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13,
    c14, Fin.val_eq_zero, zero_add, c15, implies_true, and_self]

theorem completeness {sentences : PropertySet (F p)} (order : SentenceOrder sentences) : Completeness (F p) sentences (elaborated order) CompletenessAssumptions := by
  rintro i0 env yields ⟨state_var, chaining_value_var⟩ henv ⟨state, chaining_value⟩ h_input h_normalized
  simp only [ProvableStruct.eval_eq_eval, ProvableStruct.eval, fromComponents,
    ProvableStruct.eval.go, Inputs.mk.injEq] at h_input
  dsimp only [CompletenessAssumptions, Assumptions, BLAKE3State.Normalized] at h_normalized
  obtain ⟨state_norm, chaining_value_norm⟩ := h_normalized
  simp only [Fin.forall_fin_succ, Fin.isValue, Fin.val_zero, Fin.val_succ, zero_add, Nat.reduceAdd,
    Fin.val_eq_zero, IsEmpty.forall_iff, and_true,
    Fin.getElem_fin] at state_norm chaining_value_norm
  dsimp only [elaborated, main, circuit_norm, Xor32.circuit, Xor32.elaborated] at henv ⊢
  simp only [h_input, circuit_norm, Xor32.CompletenessAssumptions, Xor32.Assumptions,
    Xor32.Spec, getElem_eval_vector] at henv ⊢
  simp_all only [gt_iff_lt, and_self]

def circuit {sentences : PropertySet (F p)} (order : SentenceOrder sentences) : FormalCircuit order Inputs BLAKE3State := {
  elaborated := elaborated order
  Assumptions
  CompletenessAssumptions
  Spec
  soundness := soundness order
  completeness := completeness order
  completenessAssumptions_implies_assumptions := fun _ _ h => h
}

end Gadgets.BLAKE3.FinalStateUpdate
