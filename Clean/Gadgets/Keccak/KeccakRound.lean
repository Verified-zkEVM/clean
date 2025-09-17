import Clean.Gadgets.Keccak.Theta
import Clean.Gadgets.Keccak.RhoPi
import Clean.Gadgets.Keccak.Chi
import Clean.Gadgets.Keccak.KeccakState
import Clean.Specs.Keccak256

namespace Gadgets.Keccak256.KeccakRound
variable {p : ℕ} [Fact p.Prime] [Fact (p > 2^16 + 2^8)]
open Specs.Keccak256

def main {sentences : PropertySet (F p)} (order : SentenceOrder sentences) (rc : UInt64) (state : Var KeccakState (F p)) : Circuit sentences (Var KeccakState (F p)) := do
  let state ← Theta.circuit order state
  let state ← RhoPi.circuit order state
  let state ← Chi.circuit order state

  -- add the round constant
  let s0 ← Xor64.circuit order ⟨state[0], const (U64.fromUInt64 rc)⟩
  return state.set 0 s0

def Assumptions (state : KeccakState (F p)) := state.Normalized

def Spec {sentences : PropertySet (F p)} (_checked : CheckedYields sentences) (rc : UInt64) (state : KeccakState (F p)) (out_state : KeccakState (F p)) :=
  out_state.Normalized
  ∧ out_state.value = keccakRound state.value rc

def elaborated {sentences : PropertySet (F p)} (order : SentenceOrder sentences) (rc : UInt64) : ElaboratedCircuit (F p) sentences KeccakState KeccakState where
  main := main order rc
  localLength _ := 1288
  output _ i0 := (Vector.mapRange 25 fun i => varFromOffset U64 (i0 + i*16 + 888) ).set 0 (varFromOffset U64 (i0 + 1280))

  localLength_eq _ _ := by simp only [main, circuit_norm, Theta.circuit, Theta.elaborated, RhoPi.circuit, RhoPi.elaborated, Chi.circuit, Chi.elaborated, Xor64.circuit, Xor64.elaborated]
  output_eq state i0 := by
    simp only [main, circuit_norm, Theta.circuit, Theta.elaborated, RhoPi.circuit, RhoPi.elaborated]
    simp only [circuit_norm, Chi.circuit, Chi.elaborated, Xor64.circuit, Xor64.elaborated, Vector.mapRange]

theorem soundness {sentences : PropertySet (F p)} (order : SentenceOrder sentences) (rc : UInt64) : Soundness (F p) (elaborated order rc) order Assumptions (Spec (rc := rc)) := by
  intro i0 env yields checked state_var state h_input state_norm h_holds

  constructor
  · sorry  -- Prove yielded sentences hold

  -- simplify goal
  apply KeccakState.normalized_value_ext
  simp only [circuit_norm, elaborated, eval_vector, keccakRound, iota]

  -- simplify constraints
  simp only [Assumptions] at state_norm
  simp only [elaborated, main, h_input, state_norm, circuit_norm,
    Theta.circuit, Theta.elaborated, RhoPi.circuit, RhoPi.elaborated, Chi.circuit, Chi.elaborated, Xor64.circuit, Xor64.elaborated,
    Theta.Assumptions, Theta.Spec, RhoPi.Assumptions, RhoPi.Spec,
    Chi.Assumptions, Chi.Spec, Xor64.Assumptions, Xor64.Spec
  ] at h_holds
  simp only [and_assoc, zero_mul, add_zero, and_imp] at h_holds

  obtain ⟨ _, theta_norm, theta_eq, h_rhopi, h_chi, h_rc ⟩ := h_holds
  have ⟨ _, rhopi_norm, rhopi_eq ⟩ := h_rhopi theta_norm
  have ⟨ _, chi_norm, chi_eq ⟩ := h_chi rhopi_norm
  rw [rhopi_eq, theta_eq] at chi_eq
  clear theta_norm theta_eq h_rhopi rhopi_eq rhopi_norm h_chi state_norm h_input

  -- simplify round constant constraint
  set state0_before_rc := eval env (varFromOffset U64 (i0 + 888))
  have h_rc_norm : state0_before_rc.Normalized := by
    simp only [KeccakState.Normalized, eval_vector, circuit_norm] at chi_norm
    exact chi_norm 0
  have h_rc_eq : state0_before_rc.value = (chi (rhoPi (theta state.value)))[0] := by
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

def CompletenessAssumptions {sentences : PropertySet (F p)} (_ : YieldContext sentences) (input : KeccakState (F p)) := Assumptions input

theorem completeness {sentences : PropertySet (F p)} (order : SentenceOrder sentences) (rc : UInt64) : Completeness (F p) sentences (elaborated order rc) CompletenessAssumptions := by
  circuit_proof_start [Theta.circuit, RhoPi.circuit, Chi.circuit, Xor64.circuit,
    Theta.Assumptions, Theta.Spec, RhoPi.Assumptions, RhoPi.Spec,
    Chi.Assumptions, Chi.Spec, Xor64.Assumptions, Xor64.Spec,
    Theta.CompletenessAssumptions, RhoPi.CompletenessAssumptions,
    Chi.CompletenessAssumptions, Xor64.CompletenessAssumptions, Assumptions]

  simp_all only [Theta.CompletenessAssumptions, RhoPi.CompletenessAssumptions,
    Chi.CompletenessAssumptions, Xor64.CompletenessAssumptions, forall_const, U64.fromUInt64_normalized, and_true, true_and]

  -- `simp_all` left one goal to pull out of hypotheses
  obtain ⟨ ⟨theta_norm, _ ⟩, h_rhopi, h_chi, _ ⟩ := h_env
  have ⟨ rhopi_norm, _ ⟩ := h_rhopi theta_norm
  have ⟨ chi_norm, _ ⟩ := h_chi rhopi_norm
  simp only [KeccakState.Normalized, eval_vector, circuit_norm] at chi_norm
  exact chi_norm 0

def circuit {sentences : PropertySet (F p)} (order : SentenceOrder sentences) (rc : UInt64) : FormalCircuit order KeccakState KeccakState := {
  elaborated := elaborated order rc
  Spec := Spec (rc := rc)
  Assumptions
  CompletenessAssumptions
  completenessAssumptions_implies_assumptions := fun _ _ h => h
  soundness := soundness order rc
  completeness := completeness order rc
}
end Gadgets.Keccak256.KeccakRound
