import Clean.Gadgets.Keccak.KeccakRound
import Clean.Specs.Keccak256
import Clean.Utils.Misc

namespace Gadgets.Keccak256.Permutation
variable {p : ℕ} [Fact p.Prime] [Fact (p > 2^16 + 2^8)]
open Specs.Keccak256

def main (state : Var KeccakState (F p)) : Circuit (F p) (Var KeccakState (F p)) :=
  .foldl roundConstants state
    fun state rc => subcircuit (KeccakRound.circuit rc) state

def assumptions (state : KeccakState (F p)) := state.is_normalized

def spec (state : KeccakState (F p)) (out_state : KeccakState (F p)) :=
  out_state.is_normalized
  ∧ out_state.value = keccak_f state.value

instance elaborated : ElaboratedCircuit (F p) KeccakState KeccakState where
  main := main
  local_length _ := 36672
  output _ i0 := (Vector.mapRange 25 fun i => var_from_offset U64 (i0 + i*16 + 36272)).set 0 (var_from_offset U64 (i0 + 36664))

  local_length_eq state i0 := by
    simp only [main, circuit_norm, KeccakRound.circuit]
  initial_offset_eq state i0 := by
    simp only [main, circuit_norm]
  output_eq state i0 := by
    simp only [main, circuit_norm, KeccakRound.circuit]
    rw [Fin.foldl_const]
    simp +arith only [Nat.cast_ofNat, Fin.coe_ofNat_eq_mod]
    ac_rfl

end Gadgets.Keccak256.Permutation
