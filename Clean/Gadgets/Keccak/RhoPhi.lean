import Clean.Circuit.Loops
import Clean.Gadgets.Rotation64.Rotation64
import Clean.Gadgets.Keccak.KeccakState
import Clean.Specs.Keccak256

namespace Gadgets.Keccak256.RhoPhi
variable {p : ℕ} [Fact p.Prime] [Fact (p > 2^16 + 2^8)]
-- instance : Fact (p > 512) := .mk (by linarith [‹Fact (p > 2^16 + 2^8)›.elim])
open Bitwise (rot_left64)

def rhoIndices : Vector (Fin 25) 25 := #v[
  0, 15, 5, 20, 10,
  6, 21, 11, 1, 16,
  12, 2, 17, 7, 22,
  18, 8, 23, 13, 3,
  24, 14, 4, 19, 9
]

def rhoShifts : Vector ℕ 25 := #v[
  0, 28, 1, 27, 62,
  44, 20, 6, 36, 55,
  43, 3, 25, 10, 39,
  21, 45, 8, 15, 41,
  14, 61, 18, 56, 2
]

-- recharacterize rho_phi as a loop
lemma rho_phi_loop (state : Vector ℕ 25) :
  Specs.Keccak256.rho_phi state =
    (rhoIndices.zip rhoShifts).map fun (i, s) => rot_left64 state[i.val] s := by
  simp only [Specs.Keccak256.rho_phi, circuit_norm]
  rw [Vector.map_mk]
  simp only
  rw [List.map_toArray]
  rfl

def main (state : Var KeccakState (F p)) : Circuit (F p) (Var KeccakState (F p)) :=
  -- TODO `circuit_norm` friendly map
  (rhoIndices.zip rhoShifts).mapM fun (i, s) =>
    subcircuit (Rotation64.circuit s) state[i.val]

end Gadgets.Keccak256.RhoPhi
