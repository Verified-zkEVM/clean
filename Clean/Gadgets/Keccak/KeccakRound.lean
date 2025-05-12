import Clean.Gadgets.Keccak.Theta
import Clean.Gadgets.Keccak.RhoPi
import Clean.Gadgets.Keccak.Chi
import Clean.Gadgets.Keccak.KeccakState
import Clean.Specs.Keccak256

namespace Gadgets.Keccak256.RoundFunction
variable {p : ℕ} [Fact p.Prime] [Fact (p > 2^16 + 2^8)]
instance : Fact (p > 512) := .mk (by linarith [‹Fact (p > _)›.elim])

def main (rc : UInt64) (state : Var KeccakState (F p)) : Circuit (F p) (Var KeccakState (F p)) := do
  let state ← subcircuit Theta.circuit state
  let state ← subcircuit RhoPi.circuit state
  let state ← subcircuit Chi.circuit state

  -- add the round constant
  let s0 ← subcircuit Xor.circuit ⟨state[0], const (U64.from_u64 rc)⟩
  return state.set 0 s0

def assumptions (state : KeccakState (F p)) := state.is_normalized

def spec (rc : UInt64) (state : KeccakState (F p)) (out_state : KeccakState (F p)) :=
  out_state.is_normalized
  ∧ out_state.value = Specs.Keccak256.keccak_round state.value rc

instance elaborated (rc : UInt64) : ElaboratedCircuit (F p) KeccakState KeccakState where
  main := main rc
  local_length _ := 1528
  output _ i0 := (Vector.mapRange 25 fun i => var_from_offset U64 (i0 + i*16 + 1128) ).set 0 (var_from_offset U64 (i0 + 1520))

  output_eq state i0 := by
    simp only [main, circuit_norm, Theta.circuit, RhoPi.circuit, Chi.circuit, Xor.circuit]

theorem soundness (rc : UInt64) : Soundness (F p) (elaborated rc) assumptions (spec rc) := by
  intro i0 env state_var state h_input state_norm h_holds

  -- simplify goal
  apply KeccakState.normalized_value_ext
  simp only [elaborated, eval_vector, Vector.getElem_map, Vector.getElem_set,
    Vector.getElem_mapRange, Specs.Keccak256.keccak_round, Specs.Keccak256.iota]

  -- simplify constraints
  simp only [assumptions] at state_norm
  simp only [main, h_input, state_norm, circuit_norm, subcircuit_norm, Theta.circuit,
    RhoPi.circuit, Chi.circuit, Xor.circuit,
    Theta.assumptions, Theta.spec,
    RhoPi.assumptions, RhoPi.spec,
    Chi.assumptions, Chi.spec,
    Xor.assumptions, Xor.spec] at h_holds
  simp only [forall_const, Nat.reduceAdd, zero_mul, add_zero, Nat.reduceMul,
    UInt64.val_val_eq_toNat, and_imp, and_assoc] at h_holds

  obtain ⟨ theta_norm, theta_eq, h_rhopi, h_chi, h_final ⟩ := h_holds
  specialize h_rhopi theta_norm
  obtain ⟨ h_rhopi_norm, h_rhopi_eq ⟩ := h_rhopi
  specialize h_chi h_rhopi_norm
  obtain ⟨ h_chi_norm, h_chi_eq ⟩ := h_chi
  rw [theta_eq] at h_rhopi_eq
  rw [h_rhopi_eq] at h_chi_eq
  clear theta_norm h_rhopi_norm theta_eq h_rhopi_eq
  rw [KeccakState.value, eval_vector] at h_chi_eq

  -- this is a hack to work around bad simplification (unfolding array before applying getElem lemmas)
  -- TODO fix this with priority / ↑ in simp attributes
  have h_out : (Vector.mapRange 25 fun i => var_from_offset U64 (i0 + i*16 + 1128) : Vector (Var U64 (F p)) 25) =
    .mapRange 25 fun i => var_from_offset U64 (i0 + i*16 + 1128) := rfl
  conv at h_out => lhs; simp only [circuit_norm]
  rw [h_out] at h_chi_eq h_chi_norm
  clear h_out

  have norm_final : (eval env (var_from_offset U64 (i0 + 520 + 600 + 8))).is_normalized := by
    simp only [KeccakState.is_normalized, eval_vector, circuit_norm] at h_chi_norm
    exact h_chi_norm 0
  have eq_final : (eval env (var_from_offset U64 (i0 + 520 + 600 + 8))).value =
    (Specs.Keccak256.chi (Specs.Keccak256.rho_pi (Specs.Keccak256.theta state.value)))[0] := by
    simp only [Vector.ext_iff] at h_chi_eq
    specialize h_chi_eq 0 (by linarith)
    simpa using h_chi_eq
  simp only [norm_final, U64.from_u64_normalized, U64.value_from_u64_eq, forall_const] at h_final
  rw [eq_final] at h_final
  simp only [zero_mul, add_zero, Nat.reduceMul, Vector.size_toArray, Nat.zero_mod, UInt64.val_val_eq_toNat]

  intro i
  by_cases hi : 0 = i.val
  · simp [circuit_norm, hi, h_final]
  simp only [hi, reduceIte]
  simp only [Vector.ext_iff, Vector.getElem_map, Vector.getElem_mapRange] at h_chi_eq
  simp only [KeccakState.is_normalized, eval_vector, Vector.getElem_map, Vector.getElem_mapRange] at h_chi_norm
  specialize h_chi_eq i i.is_lt
  specialize h_chi_norm i
  exact ⟨ h_chi_norm, h_chi_eq ⟩

end Gadgets.Keccak256.RoundFunction
