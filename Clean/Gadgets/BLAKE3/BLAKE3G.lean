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
  local_length _ := 112
  output inputs i0 := inputs.state
      |>.set a (⟨var ⟨i0 + 64⟩, var ⟨i0 + 66⟩, var ⟨i0 + 68⟩, var ⟨i0 + 70⟩⟩)
      |>.set b (var_from_offset U32 (i0 + 108))
      |>.set c (⟨var ⟨i0 + 88⟩, var ⟨i0 + 90⟩, var ⟨i0 + 92⟩, var ⟨i0 + 94⟩⟩)
      |>.set d (var_from_offset U32 (i0 + 84))

  local_length_eq _ n := by
    simp [main, circuit_norm, Xor32.circuit, Addition32.circuit, Rotation32.circuit,
      Xor32.elaborated, Addition32.elaborated, Rotation32.elaborated]

def assumptions (input : Inputs (F p)) :=
  let { state, x, y } := input
  state.is_normalized ∧ x.is_normalized ∧ y.is_normalized

def spec (a b c d : Fin 16) (input : Inputs (F p)) (out: BLAKE3State (F p)) :=
  let { state, x, y } := input
  out.value = g state.value a b c d x.value y.value ∧ out.is_normalized

theorem soundness (a b c d : Fin 16) : Soundness (F p) (elaborated a b c d) assumptions (spec a b c d) := by
  intro i0 env ⟨state_var, x_var, y_var⟩ ⟨state, x, y⟩ h_input h_normalized h_holds
  dsimp [circuit_norm, subcircuit_norm, elaborated, main, spec,
    Addition32.circuit, Addition32.elaborated, Addition32.assumptions, Addition32.spec,
    Xor32.circuit, Xor32.elaborated, Xor32.assumptions, Xor32.spec,
    Rotation32.circuit, Rotation32.elaborated, Rotation32.assumptions, Rotation32.spec,
  ] at h_holds
  dsimp [assumptions] at h_normalized

  obtain ⟨h_state, h_x, h_y⟩ := h_normalized
  simp only [↓ProvableStruct.eval_eq_eval_struct, ProvableStruct.eval, from_components,
    ProvableStruct.eval.go, Inputs.mk.injEq] at h_input
  obtain ⟨h_state_var, h_x_var, h_y_var⟩ := h_input

  simp only [BLAKE3State.is_normalized] at h_state

  have h_state_var_getElem (i : Fin 16) : eval env state_var[i.val] = state[i.val] := by
    rw [←h_state_var]
    simp only [Fin.getElem_fin, getElem_eval_vector]

  have h_state_normalized_getElem (i : Fin 16) : state[i.val].is_normalized := by
    simp [h_state]

  -- normalize offsets
  ring_nf at h_holds ⊢
  simp [circuit_norm, h_state_var_getElem, h_x_var, h_y_var] at h_holds
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14⟩ := h_holds

  -- resolve all chains of assumptions, fortunately this is easy
  simp_all only [implies_true, forall_const]

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
    ring_nf
    simp only [BLAKE3State.value, eval_vector, Vector.map_set, Vector.map_map, ↓Vector.getElem_set,
      Vector.getElem_map, g, Fin.getElem_fin, Bitwise.add32]
    (repeat' split) <;> first
      | rw [c11.left]
        simp only [Nat.add_mod_mod, Nat.mod_add_mod, Nat.reducePow]
      | rw [c12.left]
        simp only [Nat.add_mod_mod, Nat.mod_add_mod, Nat.reducePow]
      | rw [c14.left]
        simp only [Nat.add_mod_mod, Nat.mod_add_mod, Nat.reducePow]
      | rw [c9.left]
        simp only [Nat.add_mod_mod, Nat.mod_add_mod, Nat.reducePow]
      | rw [Function.comp_apply, ←h_state_var]
        simp only [Fin.getElem_fin, getElem_eval_vector]

  · intro i
    ring_nf
    simp only [eval_vector, Vector.map_set, ↓Vector.getElem_set, ↓reduceIte]
    (repeat' split) <;> first
      | exact c11.right
      | exact c12.right
      | exact c14.right
      | exact c9.right
      | simp only [Vector.getElem_map]
        rw [h_state_var_getElem]
        exact h_state_normalized_getElem i

theorem completeness (a b c d : Fin 16) : Completeness (F p) (elaborated a b c d) assumptions := by
  rintro i0 env ⟨state_var, x_var, y_var⟩ henv ⟨state, x, y⟩ h_inputs h_normalized
  dsimp [circuit_norm, subcircuit_norm, main, elaborated,
    Addition32.circuit, Addition32.elaborated, Addition32.assumptions, Addition32.spec,
    Xor32.circuit, Xor32.elaborated, Xor32.assumptions, Xor32.spec,
    Rotation32.circuit, Rotation32.elaborated, Rotation32.assumptions, Rotation32.spec,
  ] at henv ⊢

  simp [circuit_norm] at h_inputs
  obtain ⟨h_state_var, h_x_var, h_y_var⟩ := h_inputs

  dsimp [assumptions] at h_normalized
  obtain ⟨h_state, h_x, h_y⟩ := h_normalized
  simp only [BLAKE3State.is_normalized] at h_state

  have h_state_var_getElem (i : Fin 16) : eval env state_var[i.val] = state[i.val] := by
    rw [←h_state_var]
    simp only [Fin.getElem_fin, getElem_eval_vector]

  have h_state_normalized_getElem (i : Fin 16) : state[i.val].is_normalized := by
    simp [h_state]

  ring_nf at henv
  simp [circuit_norm, h_state_var_getElem, h_x_var, h_y_var] at henv
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14⟩ := henv

  -- resolve all chains of assumptions
  simp_all only [implies_true, forall_const]

  simp only [↓ProvableStruct.eval_eq_eval_struct, ProvableStruct.eval, from_components,
    ProvableStruct.eval.go, and_true]
  ring_nf
  simp_all only [gt_iff_lt, Nat.add_mod_mod, Nat.mod_add_mod, and_self]

def circuit (a b c d : Fin 16) : FormalCircuit (F p) Inputs BLAKE3State := {
  elaborated a b c d with
  assumptions := assumptions
  spec := spec a b c d
  soundness := soundness a b c d
  completeness := completeness a b c d
}


end Gadgets.BLAKE3.G
