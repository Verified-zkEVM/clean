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

def KeccakState.Normalized (state : KeccakState (F p)) :=
  ∀ i : Fin 25, state[i.val].Normalized

def KeccakState.value (state : KeccakState (F p)) := state.map U64.value

@[reducible] def KeccakRow := ProvableVector U64 5

def KeccakRow.Normalized (row : KeccakRow (F p)) :=
  ∀ i : Fin 5, row[i.val].Normalized

def KeccakRow.value (row : KeccakRow (F p)) := row.map U64.value

@[reducible] def KeccakBlock := ProvableVector U64 RATE

def KeccakBlock.Normalized (block : KeccakBlock (F p)) :=
  ∀ i : Fin RATE, block[i.val].Normalized

def KeccakBlock.value (block : KeccakBlock (F p)) := block.map U64.value

-- lemmas

def KeccakRow.normalized_iff (row : KeccakRow (F p)) :
    row.Normalized ↔
    row[0].Normalized ∧
    row[1].Normalized ∧
    row[2].Normalized ∧
    row[3].Normalized ∧
    row[4].Normalized := by
  simp [KeccakRow.Normalized, IsEmpty.forall_iff, Fin.forall_fin_succ]

-- many of our specs are of the form `state.Normalized ∧ state.value = ...` and soundness proofs use this lemma
omit [Fact (Nat.Prime p)] p_large_enough in
lemma KeccakState.normalized_value_ext (state : KeccakState (F p)) (rhs : Vector ℕ 25) :
  (∀ i : Fin 25, state[i.val].Normalized ∧ state[i.val].value = rhs[i.val]) →
    state.Normalized ∧ state.value = rhs := by
  intro h
  constructor
  · intro i
    exact (h i).left
  simp only [Vector.ext_iff, value, Vector.getElem_map]
  intro i hi
  exact (h ⟨ i, hi ⟩).right

omit [Fact (Nat.Prime p)] p_large_enough in
lemma KeccakRow.normalized_value_ext (row : KeccakRow (F p)) (rhs : Vector ℕ 5) :
  (∀ i : Fin 5, row[i.val].Normalized ∧ row[i.val].value = rhs[i.val]) →
    row.Normalized ∧ row.value = rhs := by
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
  Assumptions _ := True
  Spec block := block.Normalized
  localLength_eq _ _ := by simp +arith only [circuit_norm, U64.AssertNormalized.circuit]
  soundness := by
    simp only [circuit_norm, U64.AssertNormalized.circuit]
    simp [getElem_eval_vector, KeccakBlock.Normalized]
  completeness := by
    simp only [circuit_norm, U64.AssertNormalized.circuit]
    simp [getElem_eval_vector, KeccakBlock.Normalized]

end Gadgets.Keccak256
