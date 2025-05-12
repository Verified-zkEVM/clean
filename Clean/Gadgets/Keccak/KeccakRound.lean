import Clean.Gadgets.Keccak.Theta
import Clean.Gadgets.Keccak.RhoPi
import Clean.Gadgets.Keccak.Chi
import Clean.Gadgets.Keccak.KeccakState
import Clean.Specs.Keccak256

namespace Gadgets.Keccak256.RoundFunction
variable {p : ℕ} [Fact p.Prime] [Fact (p > 2^16 + 2^8)]
instance : Fact (p > 512) := .mk (by linarith [‹Fact (p > _)›.elim])

def main (rc : UInt64) (state : Var KeccakState (F p)) : Circuit (F p) (Var KeccakState (F p)) := do
  let rc' := U64.decompose_nat rc.val

  let state ← subcircuit Theta.circuit state
  let state ← subcircuit RhoPi.circuit state
  let state ← subcircuit Chi.circuit state

  -- add the round constant
  let s0 ← subcircuit Xor.circuit ⟨state[0], const rc'⟩
  return state.set 0 s0

def assumptions (state : KeccakState (F p)) := state.is_normalized

def spec (rc : U64 (F p)) (state : KeccakState (F p)) (out_state : KeccakState (F p)) :=
  out_state.is_normalized
  ∧ out_state.value = Specs.Keccak256.keccak_round state.value rc.value

def elaborated (rc : UInt64) : ElaboratedCircuit (F p) KeccakState KeccakState where
  main := main rc
  local_length _ := 1528
  output _ i0 := (Vector.mapRange 25 fun i => var_from_offset U64 (i0 + i*16 + 1128) ).set 0 (var_from_offset U64 (i0 + 1520))

  output_eq state i0 := by
    simp only [main, circuit_norm, Theta.circuit, RhoPi.circuit, Chi.circuit, Xor.circuit]
end Gadgets.Keccak256.RoundFunction
