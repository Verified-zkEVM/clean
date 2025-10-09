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

def main (a b c d : Fin 16) (input : Var Inputs (F p)) : Circuit (F p) (Var BLAKE3State (F p)) := do
  let { state, x, y } := input

  let state_a ← Addition32.circuit ⟨state[a], ← Addition32.circuit ⟨state[b], x⟩⟩

  let state_d ← Rotation32.circuit 16 <|
    ← Xor32.circuit ⟨state[d], state_a⟩

  let state_c ← Addition32.circuit ⟨state[c], state_d⟩

  let state_b ← Rotation32.circuit 12 <|
    ← Xor32.circuit ⟨state[b], state_c⟩

  let state_a ← Addition32.circuit ⟨state_a, ← Addition32.circuit ⟨state_b, y⟩⟩

  let state_d ← Rotation32.circuit 8 <|
    ← Xor32.circuit ⟨state_d, state_a⟩

  let state_c ← Addition32.circuit ⟨state_c, state_d⟩

  let state_b ← Rotation32.circuit 7 <|
    ← Xor32.circuit ⟨state_b, state_c⟩

  return state
    |>.set a state_a
    |>.set b state_b
    |>.set c state_c
    |>.set d state_d

instance elaborated (a b c d : Fin 16): ElaboratedCircuit (F p) Inputs BLAKE3State where
  main := main a b c d
  localLength _ := 96
  yields_eq := by intros; simp [circuit_norm, main, Addition32.circuit, Addition32.elaborated, Rotation32.circuit, Rotation32.elaborated, Xor32.circuit, Xor32.elaborated]
  output inputs i0 := (inputs.state : Vector (U32 (Expression (F p))) 16)
    |>.set a (⟨var ⟨i0 + 56⟩, var ⟨i0 + 58⟩, var ⟨i0 + 60⟩, var ⟨i0 + 62⟩⟩) a.is_lt
    |>.set b (Rotation32.output 7 (i0 + 88)) b.is_lt
    |>.set c (⟨var ⟨i0 + 76⟩, var ⟨i0 + 78⟩, var ⟨i0 + 80⟩, var ⟨i0 + 82⟩⟩) c.is_lt
    |>.set d (Rotation32.output 8 (i0 + 68)) d.is_lt

  localLength_eq _ n := by
    dsimp only [main, circuit_norm, Xor32.circuit, Addition32.circuit, Rotation32.circuit, Rotation32.elaborated]
  output_eq _ _ := by
    dsimp only [main, circuit_norm, Xor32.circuit, Addition32.circuit, Rotation32.circuit, Rotation32.elaborated]
  subcircuitsConsistent _ _ := by
    simp only [main, circuit_norm, Xor32.circuit, Addition32.circuit, Rotation32.circuit, Rotation32.elaborated]
    ring_nf; trivial

def Assumptions (input : Inputs (F p)) (_ : Set (NamedList (F p))) :=
  let { state, x, y } := input
  state.Normalized ∧ x.Normalized ∧ y.Normalized

def Spec (a b c d : Fin 16) (input : Inputs (F p)) (out : BLAKE3State (F p)) (_ : Set (NamedList (F p))) :=
  let { state, x, y } := input
  out.value = g state.value a b c d x.value y.value ∧ out.Normalized

theorem soundness (a b c d : Fin 16) : Soundness (F p) (elaborated a b c d) Assumptions (Spec a b c d) := by
  circuit_proof_start [BLAKE3State.Normalized, Xor32.circuit, Addition32.circuit, Rotation32.circuit, Rotation32.elaborated, and_imp,
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
    · rw [c11.left]
    · simp only [circuit_norm]
      rw [c12.left]
    · rw [c14.left]
    · simp only [circuit_norm]
      rw [c9.left]
    · rw [Function.comp_apply, ←h_input.left, getElem_eval_vector]

  · intro i
    simp only [eval_vector, Vector.map_set, ↓Vector.getElem_set]
    repeat' split
    · exact c11.right
    · exact c12.right
    · exact c14.right
    · exact c9.right
    · simp only [Vector.getElem_map, getElem_eval_vector, h_input, h_assumptions]

theorem completeness (a b c d : Fin 16) : Completeness (F p) (elaborated a b c d) Assumptions := by
  circuit_proof_start [BLAKE3State.Normalized]

  dsimp only [main, circuit_norm, Xor32.circuit, Addition32.circuit, Rotation32.circuit, Rotation32.elaborated] at h_env ⊢
  simp only [circuit_norm, and_imp,
    Addition32.Assumptions, Addition32.Spec, Rotation32.Assumptions, Rotation32.Spec,
    Xor32.Assumptions, Xor32.Spec, getElem_eval_vector] at h_env ⊢

  -- resolve all chains of assumptions
  simp_all only [forall_const, and_true]

def circuit (a b c d : Fin 16) : FormalCircuit (F p) Inputs BLAKE3State := {
  elaborated a b c d with
  Assumptions
  Spec := Spec a b c d
  soundness := soundness a b c d
  completeness := completeness a b c d
}

end Gadgets.BLAKE3.G
