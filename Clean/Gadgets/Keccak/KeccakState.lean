import Clean.Types.U64
import Clean.Circuit.Provable
import Clean.Utils.Field
import Clean.Specs.Keccak256

namespace Gadgets.Keccak256
open Specs.Keccak256

variable {p : ℕ} [Fact p.Prime]
variable [p_large_enough: Fact (p > 512)]

-- definitions

@[reducible] def KeccakState := ProvableVector U64 25

def KeccakState.is_normalized (state : KeccakState (F p)) :=
  ∀ i : Fin 25, state[i.val].is_normalized

def KeccakState.value (state : KeccakState (F p)) := state.map U64.value

@[reducible] def KeccakRow := ProvableVector U64 5

def KeccakRow.is_normalized (row : KeccakRow (F p)) :=
  ∀ i : Fin 5, row[i.val].is_normalized

def KeccakRow.value (row : KeccakRow (F p)) := row.map U64.value

@[reducible] def KeccakBlock := ProvableVector U64 RATE

def KeccakBlock.is_normalized (block : KeccakBlock (F p)) :=
  ∀ i : Fin RATE, block[i.val].is_normalized

def KeccakBlock.value (block : KeccakBlock (F p)) := block.map U64.value

-- lemmas

def KeccakRow.is_normalized_iff (row : KeccakRow (F p)) :
    row.is_normalized ↔
    row[0].is_normalized ∧
    row[1].is_normalized ∧
    row[2].is_normalized ∧
    row[3].is_normalized ∧
    row[4].is_normalized := by
  simp [KeccakRow.is_normalized, IsEmpty.forall_iff, Fin.forall_fin_succ]

-- many of our specs are of the form `state.is_normalized ∧ state.value = ...` and soundness proofs use this lemma
omit [Fact (Nat.Prime p)] p_large_enough in
lemma KeccakState.normalized_value_ext (state : KeccakState (F p)) (rhs : Vector ℕ 25) :
  (∀ i : Fin 25, state[i.val].is_normalized ∧ state[i.val].value = rhs[i.val]) →
    state.is_normalized ∧ state.value = rhs := by
  intro h
  constructor
  · intro i
    exact (h i).left
  simp only [Vector.ext_iff, value, Vector.getElem_map]
  intro i hi
  exact (h ⟨ i, hi ⟩).right

omit [Fact (Nat.Prime p)] p_large_enough in
lemma KeccakRow.normalized_value_ext (row : KeccakRow (F p)) (rhs : Vector ℕ 5) :
  (∀ i : Fin 5, row[i.val].is_normalized ∧ row[i.val].value = rhs[i.val]) →
    row.is_normalized ∧ row.value = rhs := by
  intro h
  constructor
  · intro i
    exact (h i).left
  simp only [Vector.ext_iff, value, Vector.getElem_map]
  intro i hi
  exact (h ⟨ i, hi ⟩).right

-- circuits

def KeccakBlock.normalized : FormalAssertion (F p) KeccakBlock where
  main block := .forEach block (assertion U64.AssertNormalized.circuit)
  assumptions _ := True
  spec block := block.is_normalized
  local_length_eq _ _ := by simp +arith only [circuit_norm, U64.AssertNormalized.circuit]
  soundness := by
    simp only [circuit_norm, U64.AssertNormalized.circuit]
    dsimp only [subcircuit_norm, U64.AssertNormalized.assumptions, U64.AssertNormalized.spec]
    simp [getElem_eval_vector, KeccakBlock.is_normalized]
  completeness := by
    simp only [circuit_norm, U64.AssertNormalized.circuit]
    dsimp only [subcircuit_norm, U64.AssertNormalized.assumptions, U64.AssertNormalized.spec]
    simp [getElem_eval_vector, KeccakBlock.is_normalized]

end Gadgets.Keccak256
