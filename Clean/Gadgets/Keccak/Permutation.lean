import Clean.Gadgets.Keccak.KeccakRound
import Clean.Specs.Keccak256

namespace Gadgets.Keccak256.Permutation
variable {p : ℕ} [Fact p.Prime] [Fact (p > 2^16 + 2^8)]
open Specs.Keccak256

def main (state : Var KeccakState (F p)) : Circuit (F p) (Var KeccakState (F p)) :=
  .foldl roundConstants state
    fun state rc => KeccakRound.circuit rc state

def Assumptions (state : KeccakState (F p)) := state.Normalized

def Spec (state : KeccakState (F p)) (out_state : KeccakState (F p)) :=
  out_state.Normalized
  ∧ out_state.value = keccakPermutation state.value

/-- state in the ith round, starting from offset n -/
def stateVar (n : ℕ) (i : ℕ) : Var KeccakState (F p) :=
  Vector.mapRange 25 (fun j => varFromOffset U64 (n + i * 1288 + j * 16 + 888))
  |>.set 0 (varFromOffset U64 (n + i * 1288 + 1280))

-- NOTE: this linter times out and blows up memory usage
set_option linter.constructorNameAsVariable false

instance elaborated : ElaboratedCircuit (F p) KeccakState KeccakState where
  main
  localLength _ := 30912
  output _ i0 := stateVar i0 23

  localLength_eq state i0 := by simp only [main, circuit_norm, KeccakRound.circuit]
  localAdds_eq _ _ _ := by
    simp [circuit_norm, main, KeccakRound.circuit, Operations.collectAdds]
    sorry
  subcircuitsConsistent state i0 := by simp only [main, circuit_norm]
  output_eq state i0 := by simp only [main, stateVar, circuit_norm, KeccakRound.circuit]

-- interestingly, `Fin.foldl` is defeq to `List.foldl`. the proofs below use this fact!
example (state : Vector ℕ 25) :
  Fin.foldl 24 (fun state j => keccakRound state roundConstants[j]) state
  = roundConstants.foldl keccakRound state := rfl

theorem soundness : Soundness (F p) elaborated Assumptions Spec := by
  intro n env initial_state_var initial_state h_input h_assumptions h_holds

  -- simplify
  simp only [main, circuit_norm, Spec,
    KeccakRound.circuit, KeccakRound.elaborated,
    KeccakRound.Spec, KeccakRound.Assumptions] at h_holds ⊢
  simp only [h_input] at h_holds
  obtain ⟨ h_init, h_succ ⟩ := h_holds
  specialize h_init h_assumptions

  -- clean up formulation
  let state (i : ℕ) : KeccakState (F p) := eval env (stateVar n i)

  change (state 0).Normalized ∧
    (state 0).value = keccakRound initial_state.value roundConstants[0]
  at h_init

  change ∀ (i : ℕ) (hi : i + 1 < 24), (state i).Normalized → (state (i + 1)).Normalized ∧
    (state (i + 1)).value = keccakRound (state i).value roundConstants[i + 1]
  at h_succ

  -- inductive proof
  have h_inductive (i : ℕ) (hi : i < 24) :
    (state i).Normalized ∧ (state i).value =
      Fin.foldl (i + 1) (fun state j => keccakRound state roundConstants[j.val]) initial_state.value := by
    induction i with
    | zero => simp [Fin.foldl_succ, h_init]
    | succ i ih =>
      have hi' : i < 24 := Nat.lt_of_succ_lt hi
      specialize ih hi'
      specialize h_succ i hi ih.left
      use h_succ.left
      rw [h_succ.right, Fin.foldl_succ_last, ih.right]
      simp
  exact h_inductive 23 (by norm_num)

theorem completeness : Completeness (F p) elaborated Assumptions := by
  intro n env initial_state_var h_env initial_state h_input h_assumptions

  -- simplify
  dsimp only [Assumptions] at h_assumptions
  simp only [main, h_input, h_assumptions, circuit_norm, KeccakRound.circuit,
    KeccakRound.elaborated, KeccakRound.Spec,
    KeccakRound.Assumptions] at h_env ⊢

  obtain ⟨ h_init, h_succ ⟩ := h_env
  replace h_init := h_init.left
  replace h_succ := fun i hi ih => (h_succ i hi ih).left

  intro i hi

  -- clean up formulation
  let state (i : ℕ) : KeccakState (F p) := eval env (stateVar n i)

  change (state 0).Normalized at h_init

  change ∀ (i : ℕ) (hi : i + 1 < 24),
    (state i).Normalized → (state (i + 1)).Normalized
  at h_succ

  change (state i).Normalized

  -- inductive proof
  have h_norm (i : ℕ) (hi : i < 24) : (state i).Normalized := by
    induction i with
    | zero => exact h_init
    | succ i ih =>
      have hi' : i < 24 := Nat.lt_of_succ_lt hi
      specialize ih hi'
      exact h_succ i hi ih
  exact h_norm i (Nat.lt_of_succ_lt hi)

def circuit : FormalCircuit (F p) KeccakState KeccakState := {
  elaborated with
  Assumptions, Spec, soundness
  -- TODO why does this time out??
  -- completeness
  completeness := by simp only [completeness]
}

end Gadgets.Keccak256.Permutation
