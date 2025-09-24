import Clean.Gadgets.Keccak.KeccakRound
import Clean.Specs.Keccak256

namespace Gadgets.Keccak256.Permutation
variable {p : ℕ} [Fact p.Prime] [Fact (p > 2^16 + 2^8)]
open Specs.Keccak256

def main {sentences : PropertySet (F p)} (order : SentenceOrder sentences) (state : Var KeccakState (F p)) : Circuit sentences (Var KeccakState (F p)) :=
  .foldl roundConstants state
    fun state rc => KeccakRound.circuit order rc state

def Assumptions (state : KeccakState (F p)) := state.Normalized

def Spec {sentences : PropertySet (F p)} (_checked : CheckedYields sentences) (state : KeccakState (F p)) (out_state : KeccakState (F p)) :=
  out_state.Normalized
  ∧ out_state.value = keccakPermutation state.value

/-- state in the ith round, starting from offset n -/
def stateVar (n : ℕ) (i : ℕ) : Var KeccakState (F p) :=
  Vector.mapRange 25 (fun j => varFromOffset U64 (n + i * 1288 + j * 16 + 888))
  |>.set 0 (varFromOffset U64 (n + i * 1288 + 1280))

-- NOTE: this linter times out and blows up memory usage
set_option linter.constructorNameAsVariable false

def elaborated {sentences : PropertySet (F p)} (order : SentenceOrder sentences) : ElaboratedCircuit (F p) sentences KeccakState KeccakState where
  main := main order
  localLength _ := 30912
  output _ i0 := stateVar i0 23
  yields _ _ _ := ∅

  localLength_eq state i0 := by simp only [main, circuit_norm, KeccakRound.circuit, KeccakRound.elaborated]
  yields_eq := by
    intros _ _ _
    simp only [main, circuit_norm, ElaboratedCircuit.yields_eq]
    simp [KeccakRound.circuit, KeccakRound.elaborated]
  subcircuitsConsistent state i0 := by simp only [main, circuit_norm]
  output_eq state i0 := by simp only [main, stateVar, circuit_norm, KeccakRound.circuit, KeccakRound.elaborated]

-- interestingly, `Fin.foldl` is defeq to `List.foldl`. the proofs below use this fact!
example (state : Vector ℕ 25) :
  Fin.foldl 24 (fun state j => keccakRound state roundConstants[j]) state
  = roundConstants.foldl keccakRound state := rfl

theorem soundness {sentences : PropertySet (F p)} (order : SentenceOrder sentences) : Soundness (F p) (elaborated order) order Assumptions Spec := by
  intro n env yields checked initial_state_var initial_state h_input h_assumptions h_holds
  constructor
  · simp [elaborated]

  -- simplify
  simp only [elaborated, main, circuit_norm, Spec,
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

def CompletenessAssumptions {sentences : PropertySet (F p)} (_ : YieldContext sentences) (input : KeccakState (F p)) := Assumptions input

theorem completeness {sentences : PropertySet (F p)} (order : SentenceOrder sentences) : Completeness (F p) sentences (elaborated order) CompletenessAssumptions := by
  intro n env yields initial_state_var h_env initial_state h_input h_assumptions

  -- simplify
  dsimp only [CompletenessAssumptions, Assumptions] at h_assumptions
  simp only [elaborated, main, h_input, h_assumptions, circuit_norm,
    KeccakRound.circuit, KeccakRound.elaborated,
    KeccakRound.Spec, KeccakRound.CompletenessAssumptions, KeccakRound.Assumptions] at h_env ⊢

  -- only keep the statements about normalization
  obtain ⟨ h_init, h_succ ⟩ := h_env
  replace h_init := h_init.2.1
  replace h_succ := fun i hi ih => (h_succ i hi ih).2.1

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

def circuit {sentences : PropertySet (F p)} (order : SentenceOrder sentences) : FormalCircuit order KeccakState KeccakState := {
  elaborated := elaborated order
  Assumptions
  CompletenessAssumptions
  completenessAssumptions_implies_assumptions := fun _ _ h => h
  Spec
  soundness := soundness order
  -- TODO why does this time out??
  -- completeness
  completeness := by simp only [completeness]
}

end Gadgets.Keccak256.Permutation
