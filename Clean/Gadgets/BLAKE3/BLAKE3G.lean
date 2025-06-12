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


def c := main (p:=p_babybear) 0 1 2 3 {
  state := default,
  x := default,
  y := default
}
#eval! c.operations.local_length
#eval! c.output

instance elaborated (a b c d : Fin 16): ElaboratedCircuit (F p) Inputs BLAKE3State where
  main := main a b c d
  local_length _ := 112
  output inputs i0 := sorry

  local_length_eq _ n := by
    simp [main, circuit_norm, Xor32.circuit, Addition32.circuit, Rotation32.circuit,
    Xor32.elaborated, Addition32.elaborated, Rotation32.elaborated]

  subcircuits_consistent _ i := by
    simp [main, circuit_norm, Xor32.circuit, Addition32.circuit, Rotation32.circuit,
    Xor32.elaborated, Addition32.elaborated, Rotation32.elaborated]
    repeat
      try constructor
      ac_rfl

  output_eq _ i := by sorry

end Gadgets.BLAKE3.G
