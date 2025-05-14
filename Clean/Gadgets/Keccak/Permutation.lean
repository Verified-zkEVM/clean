import Clean.Gadgets.Keccak.KeccakRound
import Clean.Specs.Keccak256

namespace Gadgets.Keccak256.Permutation
variable {p : ℕ} [Fact p.Prime] [Fact (p > 2^16 + 2^8)]
open Specs.Keccak256

def main (state : Var KeccakState (F p)) : Circuit (F p) (Var KeccakState (F p)) :=
  roundConstants.foldlM (fun state rc => subcircuit (KeccakRound.circuit rc) state) state

def assumptions (state : KeccakState (F p)) := state.is_normalized

def spec (state : KeccakState (F p)) (out_state : KeccakState (F p)) :=
  out_state.is_normalized
  ∧ out_state.value = keccak_f state.value
end Gadgets.Keccak256.Permutation
