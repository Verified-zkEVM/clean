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
  simp only [KeccakState.is_normalized, Fin.getElem_fin, Fin.forall_fin_succ, Fin.isValue,
    Fin.val_zero, Fin.val_succ, zero_add, Nat.reduceAdd, Fin.val_eq_zero, IsEmpty.forall_iff,
    and_true]

@[reducible]
def KeccakRow := ProvableVector U64 5

def KeccakRow.is_normalized (slice : KeccakRow (F p)) :=
  ∀ i : Fin 5, slice[i].is_normalized

def KeccakRow.value (slice : KeccakRow (F p)) := slice.map U64.value

def KeccakRow.is_normalized_iff (slice : KeccakRow (F p)) :
    slice.is_normalized ↔
    slice[0].is_normalized ∧
    slice[1].is_normalized ∧
    slice[2].is_normalized ∧
    slice[3].is_normalized ∧
    slice[4].is_normalized := by
  simp [KeccakRow.is_normalized, IsEmpty.forall_iff, Fin.forall_fin_succ]

end Gadgets.Keccak256
