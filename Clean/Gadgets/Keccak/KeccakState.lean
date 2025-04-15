import Clean.Types.U64
import Clean.Circuit.Provable
import Clean.Utils.Field

namespace Clean.Gadgets.Keccak256

variable {p : ℕ} [Fact p.Prime]
variable [p_large_enough: Fact (p > 512)]

@[reducible] def KeccakState := ProvableVector U64 25


@[reducible]
def KeccakState_is_normalized_iff (state : KeccakState (F p)) :
    (∀ i : Fin 25, state[i].is_normalized) ↔
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
  simp only [Fin.getElem_fin, Fin.forall_fin_succ, Fin.isValue,
    Fin.val_zero, Fin.val_succ, zero_add, Nat.reduceAdd, Fin.val_eq_zero, IsEmpty.forall_iff,
    and_true]

end Clean.Gadgets.Keccak256
