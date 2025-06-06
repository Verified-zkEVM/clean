import Clean.Gadgets.Keccak.KeccakRound
import Clean.Specs.Keccak256

namespace Gadgets.Keccak256.Permutation
variable {p : ℕ} [Fact p.Prime] [Fact (p > 2^16 + 2^8)]
open Specs.Keccak256

def main (state : Var KeccakState (F p)) : Circuit (F p) (Var KeccakState (F p)) :=
  .foldl roundConstants state
    fun state rc => subcircuit (KeccakRound.circuit rc) state

def assumptions (state : KeccakState (F p)) := state.is_normalized

def spec (state : KeccakState (F p)) (out_state : KeccakState (F p)) :=
  out_state.is_normalized
  ∧ out_state.value = keccak_f state.value

/-- state in the ith round, starting from offset n -/
def state_var (n : ℕ) (i : ℕ) : Var KeccakState (F p) :=
  Vector.mapRange 25 (fun j => var_from_offset U64 (n + i * 1528 + j * 16 + 1128))
  |>.set 0 (var_from_offset U64 (n + i * 1528 + 1520))

-- NOTE: this linter times out and blows up memory usage
set_option linter.constructorNameAsVariable false

instance elaborated : ElaboratedCircuit (F p) KeccakState KeccakState where
  main
  local_length _ := 36672
  output _ i0 := state_var i0 23

  local_length_eq state i0 := by simp only [main, circuit_norm, KeccakRound.circuit]
  subcircuits_consistent state i0 := by simp only [main, circuit_norm]
  output_eq state i0 := by simp only [main, state_var, circuit_norm, KeccakRound.circuit]

theorem soundness : Soundness (F p) elaborated assumptions spec := by
  intro n env initial_state_var initial_state h_input h_assumptions h_holds

  -- simplify
  simp only [main, circuit_norm, subcircuit_norm, spec,
    KeccakRound.circuit, KeccakRound.elaborated,
    KeccakRound.spec, KeccakRound.assumptions] at h_holds ⊢
  simp only [zero_add, h_input] at h_holds
  obtain ⟨ h_init, h_succ ⟩ := h_holds
  specialize h_init h_assumptions

  -- clean up formulation
  let state (i : ℕ) : KeccakState (F p) := eval env (state_var n i)

  change (state 0).is_normalized ∧
    (state 0).value = keccak_round initial_state.value roundConstants[0]
  at h_init

  change ∀ (i : ℕ) (hi : i + 1 < 24), (state i).is_normalized → (state (i + 1)).is_normalized ∧
    (state (i + 1)).value = keccak_round (state i).value roundConstants[i + 1]
  at h_succ

  -- inductive proof
  have h_inductive (i : ℕ) (hi : i < 24) :
    (state i).is_normalized ∧ (state i).value =
      Fin.foldl (i + 1) (fun state j => keccak_round state roundConstants[↑j]) initial_state.value := by
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

theorem completeness : Completeness (F p) elaborated assumptions := by
  intro n env initial_state_var h_env initial_state h_input h_assumptions

  dsimp only [assumptions] at h_assumptions
  simp only [main, h_input, h_assumptions, circuit_norm, subcircuit_norm, spec,
    KeccakRound.circuit, KeccakRound.elaborated,
    KeccakRound.spec, KeccakRound.assumptions] at h_env ⊢

  obtain ⟨ ⟨ h_init, _ ⟩, h_succ ⟩ := h_env
  intro i hi
  have hi' : i < 24 := Nat.lt_of_succ_lt hi

  -- clean up formulation
  let state (i : ℕ) : KeccakState (F p) := eval env (state_var n i)

  change (state 0).is_normalized at h_init

  change ∀ (i : ℕ) (hi : i + 1 < 24), (state i).is_normalized → (state (i + 1)).is_normalized ∧
    (state (i + 1)).value = keccak_round (state i).value roundConstants[i + 1]
  at h_succ

  change (state i).is_normalized

  -- inductive proof
  have h_norm (i : ℕ) (hi : i < 24) : (state i).is_normalized := by
    induction i with
    | zero => exact h_init
    | succ i ih =>
      have hi' : i < 24 := Nat.lt_of_succ_lt hi
      specialize ih hi'
      specialize h_succ i hi ih
      exact h_succ.left
  exact h_norm i hi'

def circuit : FormalCircuit (F p) KeccakState KeccakState := {
  elaborated with
  assumptions, spec, soundness
  -- TODO why does this time out??
  -- completeness
  completeness := by simp only [completeness]
}

end Gadgets.Keccak256.Permutation
