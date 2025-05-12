import Clean.Circuit.Loops
import Clean.Gadgets.Rotation64.Rotation64
import Clean.Gadgets.Keccak.KeccakState
import Clean.Specs.Keccak256

namespace Gadgets.Keccak256.RhoPhi
variable {p : ℕ} [Fact p.Prime] [Fact (p > 2^16 + 2^8)]
instance : Fact (p > 512) := .mk (by linarith [‹Fact (p > _)›.elim])
open Bitwise (rot_left64)

@[reducible] def rhoPiIndices : Vector (Fin 25) 25 := #v[
  0, 15, 5, 20, 10, 6, 21, 11, 1, 16, 12, 2, 17, 7, 22, 18, 8, 23, 13, 3, 24, 14, 4, 19, 9
]

@[reducible] def rhoPiShifts : Vector ℕ 25 := #v[
  0, 28, 1, 27, 62, 44, 20, 6, 36, 55, 43, 3, 25, 10, 39, 21, 45, 8, 15, 41, 14, 61, 18, 56, 2
]

-- recharacterize rho_phi as a loop
lemma rho_pi_loop (state : Vector ℕ 25) :
  Specs.Keccak256.rho_pi state =
    (rhoPiIndices.zip rhoPiShifts).map fun (i, s) => rot_left64 state[i.val] s := by
  simp only [Specs.Keccak256.rho_pi, circuit_norm]
  rw [Vector.map_mk]
  simp only
  rw [List.map_toArray]
  rfl

def main (state : Var KeccakState (F p)) : Circuit (F p) (Var KeccakState (F p)) :=
  .map (rhoPiIndices.zip rhoPiShifts) fun (i, s) =>
    subcircuit (Rotation64.circuit s) state[i.val]

instance elaborated : ElaboratedCircuit (F p) KeccakState KeccakState where
  main
  local_length _ := 600
  output _ i0 := .mapRange 25 fun i => var_from_offset U64 (i0 + i*24 + 16)

  local_length_eq _ _ := by simp only [main, circuit_norm, Rotation64.circuit]
  initial_offset_eq _ _ := by simp only [main, circuit_norm]
  output_eq state i0 := by
    simp only [main, circuit_norm, Rotation64.circuit]
    simp
end Gadgets.Keccak256.RhoPhi
