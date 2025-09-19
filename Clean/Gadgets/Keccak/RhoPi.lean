import Clean.Circuit.Loops
import Clean.Gadgets.Rotation64.Rotation64
import Clean.Gadgets.Keccak.KeccakState
import Clean.Specs.Keccak256

namespace Gadgets.Keccak256.RhoPi
variable {p : ℕ} [Fact p.Prime] [Fact (p > 2^16 + 2^8)]
instance : Fact (p > 512) := .mk (by linarith [‹Fact (p > _)›.elim])

def rhoPiIndices : Vector (Fin 25) 25 := #v[
  0, 15, 5, 20, 10, 6, 21, 11, 1, 16, 12, 2, 17, 7, 22, 18, 8, 23, 13, 3, 24, 14, 4, 19, 9
]
def rhoPiShifts : Vector (Fin 64) 25 := #v[
  0, 28, 1, 27, 62, 44, 20, 6, 36, 55, 43, 3, 25, 10, 39, 21, 45, 8, 15, 41, 14, 61, 18, 56, 2
]
def rhoPiConstants := rhoPiIndices.zip rhoPiShifts

def main (state : Var KeccakState (F p)) : Circuit (F p) (Var KeccakState (F p)) :=
  .map rhoPiConstants fun (i, s) =>
    Rotation64.circuit (-s) state[i.val]

def Assumptions := KeccakState.Normalized (p:=p)

def Spec (state : KeccakState (F p)) (out_state : KeccakState (F p)) :=
  out_state.Normalized
  ∧ out_state.value = Specs.Keccak256.rhoPi state.value

instance elaborated : ElaboratedCircuit (F p) KeccakState KeccakState where
  main
  localLength _ := 400
  localLength_eq _ _ := by simp only [main, circuit_norm, Rotation64.circuit, Rotation64.elaborated]
  subcircuitsConsistent _ _ := by simp only [main, circuit_norm]

-- recharacterize rhoPi as a loop
lemma rhoPi_loop (state : Vector ℕ 25) :
    Specs.Keccak256.rhoPi state = rhoPiConstants.map fun (i, s) => rotLeft64 state[i.val] s := by
  simp only [Specs.Keccak256.rhoPi, circuit_norm]
  rw [Vector.map_mk]
  simp only
  rw [List.map_toArray]
  rfl

theorem soundness : Soundness (F p) elaborated Assumptions Spec := by
  intro i0 env state_var state h_input state_norm h_holds

  -- simplify goal
  apply KeccakState.normalized_value_ext
  simp only [elaborated, eval_vector, Vector.getElem_map,
    KeccakState.value, rhoPi_loop]

  -- simplify constraints
  simp only [circuit_norm, eval_vector, Vector.ext_iff] at h_input
  simp only [Assumptions, KeccakState.Normalized] at state_norm
  simp only [h_input, state_norm, main, circuit_norm,
    Rotation64.circuit, Rotation64.Assumptions, Rotation64.Spec, Rotation64.elaborated] at h_holds ⊢
  simp_all [rhoPiConstants, rotLeft64_eq_rotRight64]

theorem completeness : Completeness (F p) elaborated Assumptions := by
  intro i0 env state_var h_env state h_input state_norm

  -- simplify assumptions
  simp only [circuit_norm, eval_vector, Vector.ext_iff] at h_input
  simp only [Assumptions, KeccakState.Normalized] at state_norm

  -- simplify constraints (goal + environment) and apply assumptions
  simp_all [main, circuit_norm,
    Rotation64.circuit, Rotation64.Assumptions, Rotation64.Spec]

def circuit : FormalCircuit (F p) KeccakState KeccakState :=
  { elaborated with Assumptions, Spec, soundness, completeness }
end Gadgets.Keccak256.RhoPi
