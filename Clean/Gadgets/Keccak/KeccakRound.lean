import Clean.Gadgets.Keccak.Theta
import Clean.Gadgets.Keccak.RhoPi
import Clean.Gadgets.Keccak.Chi
import Clean.Gadgets.Keccak.KeccakState
import Clean.Specs.Keccak256

namespace Gadgets.Keccak256.KeccakRound
variable {p : ℕ} [Fact p.Prime] [Fact (p > 2^16 + 2^8)]
open Specs.Keccak256

def main (rc : UInt64) (state : Var KeccakState (F p)) : Circuit (F p) (Var KeccakState (F p)) := do
  let state ← subcircuit Theta.circuit state
  let state ← subcircuit RhoPi.circuit state
  let state ← subcircuit Chi.circuit state

  -- add the round constant
  let s0 ← subcircuit Xor64.circuit ⟨state[0], const (U64.fromUInt64 rc)⟩
  return state.set 0 s0

def assumptions (state : KeccakState (F p)) := state.Normalized

def spec (rc : UInt64) (state : KeccakState (F p)) (out_state : KeccakState (F p)) :=
  out_state.Normalized
  ∧ out_state.value = keccak_round state.value rc

instance elaborated (rc : UInt64) : ElaboratedCircuit (F p) KeccakState KeccakState where
  main := main rc
  localLength _ := 1288
  output _ i0 := (Vector.mapRange 25 fun i => varFromOffset U64 (i0 + i*16 + 888) ).set 0 (varFromOffset U64 (i0 + 1280))

  localLength_eq _ _ := by simp only [main, circuit_norm, Theta.circuit, RhoPi.circuit, Chi.circuit, Xor64.circuit]
  output_eq state i0 := by
    simp only [main, circuit_norm, Theta.circuit, RhoPi.circuit, Chi.circuit, Xor64.circuit, Vector.mapRange]

theorem soundness (rc : UInt64) : Soundness (F p) (elaborated rc) assumptions (spec rc) := by
  intro i0 env state_var state h_input state_norm h_holds

  -- simplify goal
  apply KeccakState.normalized_value_ext
  simp only [circuit_norm, elaborated, eval_vector, keccak_round, iota]

  -- simplify constraints
  simp only [assumptions] at state_norm
  simp only [main, h_input, state_norm, circuit_norm, subcircuit_norm,
    Theta.circuit, RhoPi.circuit, Chi.circuit, Xor64.circuit,
    Theta.assumptions, Theta.spec, RhoPi.assumptions, RhoPi.spec,
    Chi.assumptions, Chi.spec, Xor64.assumptions, Xor64.spec
  ] at h_holds
  simp only [and_assoc, zero_mul, add_zero, and_imp] at h_holds

  obtain ⟨ theta_norm, theta_eq, h_rhopi, h_chi, h_rc ⟩ := h_holds
  have ⟨ rhopi_norm, rhopi_eq ⟩ := h_rhopi theta_norm
  have ⟨ chi_norm, chi_eq ⟩ := h_chi rhopi_norm
  rw [rhopi_eq, theta_eq] at chi_eq
  clear theta_norm theta_eq h_rhopi rhopi_eq rhopi_norm h_chi state_norm h_input

  -- simplify round constant constraint
  set state0_before_rc := eval env (varFromOffset U64 (i0 + 888))
  have h_rc_norm : state0_before_rc.Normalized := by
    simp only [KeccakState.Normalized, eval_vector, circuit_norm] at chi_norm
    exact chi_norm 0
  have h_rc_eq : state0_before_rc.value = (chi (rho_pi (theta state.value)))[0] := by
    simp only [Vector.ext_iff] at chi_eq
    specialize chi_eq 0 (by linarith)
    rw [←chi_eq]
    simp only [state0_before_rc, KeccakState.value, eval_vector, circuit_norm]
  simp only [h_rc_norm, U64.fromUInt64_normalized, forall_const] at h_rc
  rw [h_rc_eq, U64.value_fromUInt64] at h_rc

  -- prove goal, treating the i=0 case separately
  intro i
  by_cases hi : 0 = i.val <;> simp only [hi, reduceIte]
  · simp [←hi, h_rc]
  simp only [KeccakState.value, KeccakState.Normalized, eval_vector,
    Vector.ext_iff, Vector.getElem_map, Vector.getElem_mapRange] at chi_norm chi_eq
  specialize chi_eq i i.is_lt
  specialize chi_norm i
  ring_nf at chi_eq chi_norm ⊢
  exact ⟨ chi_norm, chi_eq ⟩

theorem completeness (rc : UInt64) : Completeness (F p) (elaborated rc) assumptions := by
  intro i0 env state_var h_env state h_input state_norm

  -- simplify goal and witness hypotheses
  simp only [assumptions] at state_norm
  dsimp only [main, circuit_norm, subcircuit_norm,
    Theta.circuit, RhoPi.circuit, Chi.circuit, Xor64.circuit,
    Theta.assumptions, Theta.spec, RhoPi.assumptions, RhoPi.spec,
    Chi.assumptions, Chi.spec, Xor64.assumptions, Xor64.spec
  ] at h_env ⊢
  simp_all only [main, h_input, state_norm, circuit_norm,
    U64.fromUInt64_normalized]

  -- `simp_all` left one goal to pull out of hypotheses
  obtain ⟨ ⟨theta_norm, _ ⟩, h_rhopi, h_chi, _ ⟩ := h_env
  have ⟨ rhopi_norm, _ ⟩ := h_rhopi theta_norm
  have ⟨ chi_norm, _ ⟩ := h_chi rhopi_norm
  simp only [KeccakState.Normalized, eval_vector, circuit_norm] at chi_norm
  exact chi_norm 0

def circuit (rc : UInt64) : FormalCircuit (F p) KeccakState KeccakState := {
  elaborated rc with
  spec := spec rc
  assumptions,
  soundness := soundness rc,
  completeness := completeness rc,
}
end Gadgets.Keccak256.KeccakRound
