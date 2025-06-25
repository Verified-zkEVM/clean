import Clean.Gadgets.Xor.Xor32
import Clean.Gadgets.BLAKE3.BLAKE3State
import Clean.Gadgets.Addition32.Addition32
import Clean.Gadgets.Rotation32.Rotation32
import Clean.Specs.BLAKE3
import Clean.Circuit.Provable

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
  to_components := fun { state, x, y } => .cons state (.cons x (.cons y .nil))
  from_components := fun (.cons state (.cons x (.cons y .nil))) => { state, x, y }

def main (a b c d : Fin 16) (input : Var Inputs (F p)) : Circuit (F p) (Var BLAKE3State (F p)) := do
  let { state, x, y } := input

  let state_a ← subcircuit (Addition32.circuit) ⟨
    state[a],
    ← subcircuit (Addition32.circuit) ⟨state[b], x⟩
  ⟩

  let state_d ← subcircuit (Rotation32.circuit 16) <|
    ← subcircuit (Xor32.circuit) ⟨state[d], state_a⟩

  let state_c ← subcircuit (Addition32.circuit) ⟨state[c], state_d⟩

  let state_b ← subcircuit (Rotation32.circuit 12) <|
    ← subcircuit (Xor32.circuit) ⟨state[b], state_c⟩

  let state_a ← subcircuit (Addition32.circuit) ⟨
    state_a,
    ← subcircuit (Addition32.circuit) ⟨state_b, y⟩
  ⟩

  let state_d ← subcircuit (Rotation32.circuit 8) <|
    ← subcircuit (Xor32.circuit) ⟨state_d, state_a⟩

  let state_c ← subcircuit (Addition32.circuit) ⟨state_c, state_d⟩

  let state_b ← subcircuit (Rotation32.circuit 7) <|
    ← subcircuit (Xor32.circuit) ⟨state_b, state_c⟩

  let state := state.set a state_a
                    |>.set b state_b
                    |>.set c state_c
                    |>.set d state_d
  return state

instance elaborated (a b c d : Fin 16): ElaboratedCircuit (F p) Inputs BLAKE3State where
  main := main a b c d
  localLength _ := 96
  output inputs i0 := (inputs.state : Vector (U32 (Expression (F p))) 16)
    |>.set a (⟨var ⟨i0 + 56⟩, var ⟨i0 + 58⟩, var ⟨i0 + 60⟩, var ⟨i0 + 62⟩⟩) a.is_lt
    |>.set b (Rotation32.output 7 (i0 + 88)) b.is_lt
    |>.set c (⟨var ⟨i0 + 76⟩, var ⟨i0 + 78⟩, var ⟨i0 + 80⟩, var ⟨i0 + 82⟩⟩) c.is_lt
    |>.set d (Rotation32.output 8 (i0 + 68)) d.is_lt

  localLength_eq _ n := by
    dsimp only [main, circuit_norm, Xor32.circuit, Addition32.circuit, Rotation32.circuit, Rotation32.elaborated]
  output_eq _ _ := by
    dsimp only [main, circuit_norm, Xor32.circuit, Addition32.circuit, Rotation32.circuit, Rotation32.elaborated]
  subcircuits_consistent _ _ := by
    simp only [main, circuit_norm, Xor32.circuit, Addition32.circuit, Rotation32.circuit, Rotation32.elaborated]
    ring_nf; trivial

def assumptions (input : Inputs (F p)) :=
  let { state, x, y } := input
  state.is_normalized ∧ x.is_normalized ∧ y.is_normalized

def spec (a b c d : Fin 16) (input : Inputs (F p)) (out: BLAKE3State (F p)) :=
  let { state, x, y } := input
  out.value = g state.value a b c d x.value y.value ∧ out.is_normalized

theorem soundness (a b c d : Fin 16) : Soundness (F p) (elaborated a b c d) assumptions (spec a b c d) := by
  intro i0 env ⟨state_var, x_var, y_var⟩ ⟨state, x, y⟩ h_input h_normalized h_holds
  simp only [circuit_norm, Inputs.mk.injEq] at h_input
  dsimp only [assumptions, BLAKE3State.is_normalized] at h_normalized

  dsimp only [main, circuit_norm, Xor32.circuit, Addition32.circuit, Rotation32.circuit, Rotation32.elaborated] at h_holds
  simp only [circuit_norm, subcircuit_norm, and_imp,
    Addition32.assumptions, Addition32.spec, Rotation32.assumptions, Rotation32.spec,
    Xor32.assumptions, Xor32.spec, getElem_eval_vector, h_input] at h_holds

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
  simp only [spec, ElaboratedCircuit.output]
  constructor
  · ext i hi
    simp only [BLAKE3State.value, eval_vector, Vector.map_set, Vector.map_map, ↓Vector.getElem_set,
      Vector.getElem_map, g, Fin.getElem_fin, Bitwise.add32]
    repeat' split
    · rw [c11.left]
    · rw [c12.left]
    · rw [c14.left]
    · rw [c9.left]
    · rw [Function.comp_apply, ←h_input.left, getElem_eval_vector]

  · intro i
    simp only [eval_vector, Vector.map_set, ↓Vector.getElem_set]
    repeat' split
    · exact c11.right
    · exact c12.right
    · exact c14.right
    · exact c9.right
    · simp only [Vector.getElem_map, getElem_eval_vector, h_input, h_normalized]

theorem completeness (a b c d : Fin 16) : Completeness (F p) (elaborated a b c d) assumptions := by
  rintro i0 env ⟨state_var, x_var, y_var⟩ henv ⟨state, x, y⟩ h_input h_normalized
  simp only [↓ProvableStruct.eval_eq_eval_struct, ProvableStruct.eval, from_components,
    ProvableStruct.eval.go, Inputs.mk.injEq] at h_input
  dsimp only [assumptions, BLAKE3State.is_normalized] at h_normalized

  dsimp only [main, circuit_norm, Xor32.circuit, Addition32.circuit, Rotation32.circuit, Rotation32.elaborated] at henv ⊢
  simp only [h_input, circuit_norm, subcircuit_norm, and_imp,
    Addition32.assumptions, Addition32.spec, Rotation32.assumptions, Rotation32.spec,
    Xor32.assumptions, Xor32.spec, getElem_eval_vector] at henv ⊢

  -- resolve all chains of assumptions
  simp_all only [implies_true, forall_const, and_true]

def circuit (a b c d : Fin 16) : FormalCircuit (F p) Inputs BLAKE3State := {
  elaborated a b c d with
  assumptions := assumptions
  spec := spec a b c d
  soundness := soundness a b c d
  completeness := completeness a b c d
}


end Gadgets.BLAKE3.G
