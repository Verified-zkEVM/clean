import Clean.Types.U64
import Clean.Circuit.Provable
import Clean.Utils.Field

namespace Gadgets.Keccak256

variable {p : ℕ} [Fact p.Prime]
variable [p_large_enough: Fact (p > 512)]

@[reducible] def KeccakState := ProvableVector U64 25

def KeccakState.is_normalized (state : KeccakState (F p)) :=
  ∀ i : Fin 25, state[i].is_normalized

def KeccakState.value (state : KeccakState (F p)) := state.map U64.value

@[reducible] def KeccakRow := ProvableVector U64 5

def KeccakRow.is_normalized (row : KeccakRow (F p)) :=
  ∀ i : Fin 5, row[i].is_normalized

def KeccakRow.value (row : KeccakRow (F p)) := row.map U64.value

def KeccakRow.is_normalized_iff (row : KeccakRow (F p)) :
    row.is_normalized ↔
    row[0].is_normalized ∧
    row[1].is_normalized ∧
    row[2].is_normalized ∧
    row[3].is_normalized ∧
    row[4].is_normalized := by
  simp [KeccakRow.is_normalized, IsEmpty.forall_iff, Fin.forall_fin_succ]

def KeccakState.is_normalized_iff (state : KeccakState (F p)) :
    state.is_normalized ↔
    state[0].is_normalized ∧
    state[1].is_normalized ∧
    state[2].is_normalized ∧
    state[3].is_normalized ∧
    state[4].is_normalized ∧
    state[5].is_normalized ∧
    state[6].is_normalized ∧
    state[7].is_normalized ∧
    state[8].is_normalized ∧
    state[9].is_normalized ∧
    state[10].is_normalized ∧
    state[11].is_normalized ∧
    state[12].is_normalized ∧
    state[13].is_normalized ∧
    state[14].is_normalized ∧
    state[15].is_normalized ∧
    state[16].is_normalized ∧
    state[17].is_normalized ∧
    state[18].is_normalized ∧
    state[19].is_normalized ∧
    state[20].is_normalized ∧
    state[21].is_normalized ∧
    state[22].is_normalized ∧
    state[23].is_normalized ∧
    state[24].is_normalized := by
  simp [KeccakState.is_normalized, IsEmpty.forall_iff, Fin.forall_fin_succ]
end Gadgets.Keccak256
