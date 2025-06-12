import Clean.Gadgets.Xor.Xor32
import Clean.Gadgets.BLAKE3.BLAKE3State
import Clean.Gadgets.Addition32.Addition32
import Clean.Gadgets.Rotation32.Rotation32
import Clean.Specs.BLAKE3

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
    Addition32.circuit, Addition32.elaborated,
    Xor32.circuit, Xor32.elaborated,
    Rotation32.circuit, Rotation32.elaborated,
  ] at h_holds
  simp [circuit_norm, elaborated, main, spec]
  dsimp [assumptions] at h_normalized

  -- normalize offsets
  ring_nf at h_holds ⊢
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14⟩ := h_holds

  -- give names to intermediate variables for clarity
  set tmp1 : U32 (Expression (F p)) := ⟨var ⟨i0⟩, var ⟨2 + i0⟩, var ⟨4 + i0⟩, var ⟨6 + i0⟩⟩
  set state_a1 : U32 (Expression (F p)) := ⟨var ⟨8 + i0⟩, var ⟨10 + i0⟩, var ⟨12 + i0⟩, var ⟨14 + i0⟩⟩
  set tmp2 := var_from_offset U32 (16 + i0)
  set state_d1 : U32 (Expression (F p)) := ⟨var ⟨20 + i0⟩, var ⟨22 + i0⟩, var ⟨24 + i0⟩, var ⟨26 + i0⟩⟩
  set tmp3 := var_from_offset U32 (28 + i0)
  set state_c1 : U32 (Expression (F p)) := ⟨var ⟨32 + i0⟩, var ⟨34 + i0⟩, var ⟨36 + i0⟩, var ⟨38 + i0⟩⟩
  set tmp4 := var_from_offset U32 (40 + i0)
  set state_b1 := var_from_offset U32 (52 + i0)

  set tmp5 : U32 (Expression (F p)) := ⟨var ⟨56 + i0⟩, var ⟨58 + i0⟩, var ⟨60 + i0⟩, var ⟨62 + i0⟩⟩
  set state_a2 : U32 (Expression (F p)) := ⟨var ⟨64 + i0⟩, var ⟨66 + i0⟩, var ⟨68 + i0⟩, var ⟨70 + i0⟩⟩
  set tmp6 := var_from_offset U32 (72 + i0)
  set state_d2 := var_from_offset U32 (84 + i0)
  set state_c2 : U32 (Expression (F p)) := ⟨var ⟨88 + i0⟩, var ⟨90 + i0⟩, var ⟨92 + i0⟩, var ⟨94 + i0⟩⟩
  set tmp7 := var_from_offset U32 (96 + i0)
  set state_b2 := var_from_offset U32 (108 + i0)



  simp [circuit_norm, eval, Expression.eval] at c1
  constructor
  · sorry
  · sorry

theorem completeness (a b c d : Fin 16) : Completeness (F p) (elaborated a b c d) assumptions := by
  sorry


def circuit (a b c d : Fin 16) : FormalCircuit (F p) Inputs BLAKE3State := {
  elaborated a b c d with
  assumptions := assumptions
  spec := spec a b c d
  soundness := soundness a b c d
  completeness := completeness a b c d
}


end Gadgets.BLAKE3.G
