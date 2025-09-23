import Clean.Gadgets.Xor.Xor32
import Clean.Gadgets.BLAKE3.BLAKE3State
import Clean.Gadgets.Addition32.Addition32
import Clean.Gadgets.Rotation32.Rotation32
import Clean.Specs.BLAKE3
import Clean.Circuit.Provable
import Clean.Utils.Tactics

namespace Gadgets.BLAKE3.G
variable {p : ℕ} [Fact p.Prime] [p_large_enough: Fact (p > 2^16 + 2^8)]
instance : Fact (p > 512) := .mk (by linarith [p_large_enough.elim])

open Specs.BLAKE3 (g)

structure Inputs (F : Type) where
  state : BLAKE3State F
  x : U32 F
  y : U32 F

instance : ProvableStruct Inputs where
  components := [BLAKE3State, U32, U32]
  toComponents := fun { state, x, y } => .cons state (.cons x (.cons y .nil))
  fromComponents := fun (.cons state (.cons x (.cons y .nil))) => { state, x, y }

def main {sentences : PropertySet (F p)} (order : SentenceOrder sentences) (a b c d : Fin 16) (input : Var Inputs (F p)) : Circuit sentences (Var BLAKE3State (F p)) := do
  let { state, x, y } := input

  let state_a ← Addition32.circuit order ⟨state[a], ← Addition32.circuit order ⟨state[b], x⟩⟩

  let state_d ← Rotation32.circuit order 16 <|
    ← Xor32.circuit order ⟨state[d], state_a⟩

  let state_c ← Addition32.circuit order ⟨state[c], state_d⟩

  let state_b ← Rotation32.circuit order 12 <|
    ← Xor32.circuit order ⟨state[b], state_c⟩

  let state_a ← Addition32.circuit order ⟨state_a, ← Addition32.circuit order ⟨state_b, y⟩⟩

  let state_d ← Rotation32.circuit order 8 <|
    ← Xor32.circuit order ⟨state_d, state_a⟩

  let state_c ← Addition32.circuit order ⟨state_c, state_d⟩

  let state_b ← Rotation32.circuit order 7 <|
    ← Xor32.circuit order ⟨state_b, state_c⟩

  return state
    |>.set a state_a
    |>.set b state_b
    |>.set c state_c
    |>.set d state_d

def elaborated {sentences : PropertySet (F p)} (order : SentenceOrder sentences) (a b c d : Fin 16): ElaboratedCircuit (F p) sentences Inputs BLAKE3State where
  main := main order a b c d
  localLength _ := 96
  output inputs i0 := (inputs.state : Vector (U32 (Expression (F p))) 16)
    |>.set a (⟨var ⟨i0 + 56⟩, var ⟨i0 + 58⟩, var ⟨i0 + 60⟩, var ⟨i0 + 62⟩⟩) a.is_lt
    |>.set b (Rotation32.output 7 (i0 + 88)) b.is_lt
    |>.set c (⟨var ⟨i0 + 76⟩, var ⟨i0 + 78⟩, var ⟨i0 + 80⟩, var ⟨i0 + 82⟩⟩) c.is_lt
    |>.set d (Rotation32.output 8 (i0 + 68)) d.is_lt
  yields _ _ _ := ∅

  localLength_eq _ n := by
    dsimp only [main, circuit_norm, Xor32.circuit, Xor32.elaborated, Addition32.circuit, Addition32.elaborated, Rotation32.circuit, Rotation32.elaborated]
  output_eq _ _ := by
    dsimp only [main, circuit_norm, Xor32.circuit, Xor32.elaborated, Addition32.circuit, Addition32.elaborated, Rotation32.circuit, Rotation32.elaborated]
  yields_eq := by
    intros env input offset
    simp only [circuit_norm, main, ElaboratedCircuit.yields_eq]
    simp [Xor32.circuit, Addition32.circuit, Addition32.elaborated, Xor32.elaborated, Rotation32.circuit, Rotation32.elaborated]
  subcircuitsConsistent _ _ := by
    simp only [main, circuit_norm, Xor32.circuit, Xor32.elaborated, Addition32.circuit, Addition32.elaborated, Rotation32.circuit, Rotation32.elaborated]
    ring_nf; trivial

def Assumptions (input : Inputs (F p)) :=
  let { state, x, y } := input
  state.Normalized ∧ x.Normalized ∧ y.Normalized

def CompletenessAssumptions {sentences : PropertySet (F p)} (_ : YieldContext sentences) (input : Inputs (F p)) := Assumptions input

def Spec {sentences : PropertySet (F p)} (_checked : CheckedYields sentences) (a b c d : Fin 16) (input : Inputs (F p)) (out : BLAKE3State (F p)) :=
  let { state, x, y } := input
  out.value = g state.value a b c d x.value y.value ∧ out.Normalized

set_option maxHeartbeats 600000

theorem soundness {sentences : PropertySet (F p)} (order : SentenceOrder sentences) (a b c d : Fin 16) : Soundness (F p) (elaborated order a b c d) order Assumptions (Spec (a:=a) (b:=b) (c:=c) (d:=d)) := by
  circuit_proof_start [elaborated, BLAKE3State.Normalized, Xor32.circuit, Xor32.elaborated, Addition32.circuit, Addition32.elaborated, Rotation32.circuit, Rotation32.elaborated, and_imp,
    Addition32.Assumptions, Addition32.Spec, Rotation32.Assumptions, Rotation32.Spec,
    Xor32.Assumptions, Xor32.Spec, getElem_eval_vector]

  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14⟩ := h_holds

  -- resolve all chains of assumptions, fortunately this is easy
  simp_all only [forall_const]

  -- In c9, c11, c12, and c14, we now have the correct hypotheses regarding the
  -- updated values in the output state.
  -- From this point onward, we need to prove that the updated values are consistent with the spec.
  -- Unfortunately, this is not trivial because we do not require that a, b, c, and d are distinct.
  -- Therefore, there could be overwriting of values in the state update chain, requiring
  -- case-by-case reasoning on the indices.
  -- NOTE: This is not a bug, we are following the BLAKE specification of the g function verbatim.
  -- See, for example, https://www.ietf.org/archive/id/draft-aumasson-blake3-00.html#name-quarter-round-function-g
  constructor
  · ext i hi
    simp only [BLAKE3State.value, eval_vector, Vector.map_set, Vector.map_map, ↓Vector.getElem_set,
      Vector.getElem_map, g, Fin.getElem_fin, add32]
    repeat' split
    · rw [c11.2.1]
    · simp only [circuit_norm]
      rw [c12.2.1]
    · rw [c14.2.1]
    · simp only [circuit_norm]
      rw [c9.2.1]
    · rw [Function.comp_apply, ←h_input.1, getElem_eval_vector]

  · intro i
    simp only [eval_vector, Vector.map_set, ↓Vector.getElem_set]
    repeat' split
    · exact c11.2.2
    · exact c12.2.2
    · exact c14.2.2
    · exact c9.2.2
    · simp only [Vector.getElem_map, getElem_eval_vector, h_input, h_assumptions]

theorem completeness {sentences : PropertySet (F p)} (order : SentenceOrder sentences) (a b c d : Fin 16) : Completeness (F p) sentences (elaborated order a b c d) CompletenessAssumptions := by
  circuit_proof_start [elaborated, CompletenessAssumptions, Assumptions, BLAKE3State.Normalized]

  dsimp only [elaborated, main, circuit_norm, Xor32.circuit, Xor32.elaborated, Addition32.circuit, Addition32.elaborated, Rotation32.circuit, Rotation32.elaborated] at h_env ⊢
  simp only [circuit_norm, and_imp,
    Addition32.CompletenessAssumptions, Addition32.Assumptions, Addition32.Spec, Rotation32.CompletenessAssumptions, Rotation32.Assumptions, Rotation32.Spec,
    Xor32.CompletenessAssumptions, Xor32.Assumptions, Xor32.Spec, getElem_eval_vector] at h_env ⊢

  -- resolve all chains of assumptions
  simp_all only [forall_const, and_true]

def circuit {sentences : PropertySet (F p)} (order : SentenceOrder sentences) (a b c d : Fin 16) : FormalCircuit order Inputs BLAKE3State := {
  elaborated := elaborated order a b c d
  Assumptions
  CompletenessAssumptions
  Spec := Spec (a:=a) (b:=b) (c:=c) (d:=d)
  soundness := soundness order a b c d
  completeness := completeness order a b c d
  completenessAssumptions_implies_assumptions := fun _ _ h => h
}

end Gadgets.BLAKE3.G
