import Clean.Circuit.Loops
import Clean.Gadgets.Rotation64.Rotation64
import Clean.Gadgets.Keccak.KeccakState
import Clean.Specs.Keccak256

namespace Gadgets.Keccak256.RhoPi
variable {p : ℕ} [Fact p.Prime] [Fact (p > 2^16 + 2^8)]
instance : Fact (p > 512) := .mk (by linarith [‹Fact (p > _)›.elim])
open Bitwise (rot_left64)

def rhoPiIndices : Vector (Fin 25) 25 := #v[
  0, 15, 5, 20, 10, 6, 21, 11, 1, 16, 12, 2, 17, 7, 22, 18, 8, 23, 13, 3, 24, 14, 4, 19, 9
]
def rhoPiShifts : Vector ℕ 25 := #v[
  0, 28, 1, 27, 62, 44, 20, 6, 36, 55, 43, 3, 25, 10, 39, 21, 45, 8, 15, 41, 14, 61, 18, 56, 2
]
def rhoPiConstants := rhoPiIndices.zip rhoPiShifts

def main (state : Var KeccakState (F p)) : Circuit (F p) (Var KeccakState (F p)) :=
  .map rhoPiConstants fun (i, s) =>
    subcircuit (Rotation64.circuit (-s)) state[i.val]

def assumptions := KeccakState.is_normalized (p:=p)

def spec (state : KeccakState (F p)) (out_state : KeccakState (F p)) :=
  out_state.is_normalized
  ∧ out_state.value = Specs.Keccak256.rho_pi state.value

instance elaborated : ElaboratedCircuit (F p) KeccakState KeccakState where
  main
  local_length _ := 600
  output _ i0 := .mapRange 25 fun i => var_from_offset U64 (i0 + i*24 + 16)

  local_length_eq _ _ := by simp only [main, circuit_norm, Rotation64.circuit, Rotation64.elaborated]
  subcircuits_consistent _ _ := by simp only [main, circuit_norm]
  output_eq state i0 := by
    simp only [main, circuit_norm, Rotation64.circuit, Vector.mapRange, Rotation64.elaborated]
    simp only [rhoPiConstants, rhoPiIndices, rhoPiShifts, Vector.mk_zip_mk, List.zip_toArray, Vector.mapIdx_mk, List.mapIdx_toArray]
    simp only [List.zip_cons_cons, List.zip_nil_right]
    simp only [List.mapIdx_cons, List.mapIdx_nil]

-- recharacterize rho_phi as a loop
lemma rho_pi_loop (state : Vector ℕ 25) :
  Specs.Keccak256.rho_pi state =
    rhoPiConstants.map fun (i, s) => rot_left64 state[i.val] s := by
  simp only [Specs.Keccak256.rho_pi, circuit_norm]
  rw [Vector.map_mk]
  simp only
  rw [List.map_toArray]
  rfl

theorem soundness : Soundness (F p) elaborated assumptions spec := by
  intro i0 env state_var state h_input state_norm h_holds

  -- simplify goal
  apply KeccakState.normalized_value_ext
  simp only [spec, elaborated, rho_pi_loop, eval_vector, KeccakState.value,
    Vector.getElem_map, Vector.getElem_mapRange, Vector.getElem_mapFinRange]

  -- simplify constraints
  simp only [circuit_norm, eval_vector, Vector.ext_iff] at h_input
  simp only [assumptions, KeccakState.is_normalized] at state_norm
  simp only [h_input, state_norm, main, circuit_norm, subcircuit_norm,
    Rotation64.circuit, Rotation64.assumptions, Rotation64.spec, Rotation64.elaborated] at h_holds
  simp_all [Bitwise.rot_left_eq_rot_right]

theorem completeness : Completeness (F p) elaborated assumptions := by
  intro i0 env state_var h_env state h_input state_norm

  -- simplify assumptions
  simp only [circuit_norm, eval_vector, Vector.ext_iff] at h_input
  simp only [assumptions, KeccakState.is_normalized] at state_norm

  -- simplify constraints (goal + environment) and apply assumptions
  simp_all [state_norm, h_input, main, circuit_norm, subcircuit_norm,
    Rotation64.circuit, Rotation64.assumptions, Rotation64.spec]

def circuit : FormalCircuit (F p) KeccakState KeccakState := {
  elaborated with assumptions, spec, soundness, completeness
}
end Gadgets.Keccak256.RhoPi
