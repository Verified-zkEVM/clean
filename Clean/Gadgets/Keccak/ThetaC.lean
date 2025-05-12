import Clean.Circuit.Loops
import Clean.Gadgets.Addition8.Addition8FullCarry
import Clean.Types.U64
import Clean.Gadgets.Addition32.Theorems
import Clean.Gadgets.Xor.Xor64
import Clean.Gadgets.Keccak.KeccakState
import Clean.Specs.Keccak256

namespace Gadgets.Keccak256.ThetaC
variable {p : ℕ} [Fact p.Prime] [Fact (p > 512)]

def main (state : Var KeccakState (F p)) : Circuit (F p) (Var KeccakRow (F p)) :=
  .mapFinRange 5 fun i => do
    let c ← subcircuit Xor.circuit ⟨state[5*i.val], state[5*i.val + 1]⟩
    let c ← subcircuit Xor.circuit ⟨c, state[5*i.val + 2]⟩
    let c ← subcircuit Xor.circuit ⟨c, state[5*i.val + 3]⟩
    let c ← subcircuit Xor.circuit ⟨c, state[5*i.val + 4]⟩
    return c

def assumptions (state : KeccakState (F p)) := state.is_normalized

def spec (state : KeccakState (F p)) (out: KeccakRow (F p)) :=
  out.is_normalized
  ∧ out.value = Specs.Keccak256.theta_c state.value

-- #eval! theta_c (p:=p_babybear) default |>.operations.local_length
-- #eval! theta_c (p:=p_babybear) default |>.output
instance elaborated : ElaboratedCircuit (F p) KeccakState KeccakRow where
  main
  local_length _ := 160
  output _ i0 := .mapRange 5 fun i => var_from_offset U64 (i0 + i*32 + 24)

  local_length_eq _ _ := by simp only [main, circuit_norm, Xor.circuit]
  initial_offset_eq _ _ := by simp only [main, circuit_norm]
  output_eq _ _ := by simp only [main, circuit_norm, Xor.circuit]

-- rewrite theta_c as a loop
lemma theta_c_loop (state : Vector ℕ 25) :
    Specs.Keccak256.theta_c state = .mapFinRange 5 fun i =>
      state[5*i.val] ^^^ state[5*i.val + 1] ^^^ state[5*i.val + 2] ^^^ state[5*i.val + 3] ^^^ state[5*i.val + 4] := by
  rw [Specs.Keccak256.theta_c, Vector.mapFinRange, Vector.finRange, Vector.map_mk, Vector.eq_mk, List.map_toArray]
  rfl

theorem soundness : Soundness (F p) elaborated assumptions spec := by
  intro i0 env state_var state h_input state_norm h_holds

  -- rewrite goal
  apply KeccakRow.normalized_value_ext
  simp only [elaborated, theta_c_loop, eval_vector, KeccakState.value,
    Vector.getElem_map, Vector.getElem_mapFinRange, Vector.getElem_mapRange]

  -- simplify constraints
  simp only [circuit_norm, eval_vector, Vector.ext_iff] at h_input
  simp only [circuit_norm, subcircuit_norm, h_input, eval_vector,
    main, Xor.circuit, Xor.assumptions, Xor.spec] at h_holds
  simp only [and_assoc, Nat.reduceAdd, Nat.reduceMod] at h_holds
  have state_norm : ∀ {i : ℕ} (hi : i < 25), state[i].is_normalized :=
    fun hi => state_norm ⟨ _, hi ⟩
  simp only [state_norm, and_self, forall_const, and_true] at h_holds

  intro i
  specialize h_holds i
  aesop

theorem completeness : Completeness (F p) elaborated assumptions := by
  intro i0 env state_var h_env state h_input h_assumptions
  simp only [circuit_norm, subcircuit_norm, assumptions, eval_vector,
    main, Xor.circuit, Xor.assumptions, Xor.spec] at h_input h_assumptions ⊢
  simp only [add_assoc, Nat.reduceAdd, Nat.reduceMod]

  rw [KeccakState.is_normalized] at h_assumptions
  have s {i : ℕ} (hi : i < 25) : (eval env state_var[i]).is_normalized = True := by
    have : eval env state_var[i] = state[i] := by rw [←h_input, Vector.getElem_map]
    rw [this, eq_iff_iff, iff_true]
    exact h_assumptions ⟨ i, hi ⟩
  simp only [s, true_and, and_true]

  dsimp only [Environment.uses_local_witnesses, elaborated] at h_env
  -- simp only [theta_c, circuit_norm] at h_env
  sorry

def circuit : FormalCircuit (F p) KeccakState KeccakRow := {
  elaborated with assumptions, spec, soundness, completeness
}

end Gadgets.Keccak256.ThetaC
