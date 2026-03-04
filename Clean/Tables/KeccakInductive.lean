/- Simple Keccak example using `InductiveTable` -/
import Clean.Table.Inductive
import Clean.Circuit.Extensions
import Clean.Circuit.FreshVars
import Clean.Gadgets.Keccak.AbsorbBlock
import Clean.Specs.Keccak256
open Specs.Keccak256
variable {p : ℕ} [Fact p.Prime] [Fact (p > 2 ^ 16 + 2 ^ 8)]

namespace Tables.KeccakInductive
open Gadgets.Keccak256

set_option maxHeartbeats 400000 in
def table : InductiveTable (F p) KeccakState KeccakBlock where
  step state block := do
    KeccakBlock.normalized block
    AbsorbBlock.circuit { state, block }

  Spec _ blocks i _ state _ : Prop :=
    state.Normalized
    ∧ state.value = absorbBlocks (blocks.map KeccakBlock.value)

  InputAssumptions i block _ := block.Normalized

  soundness := by
    intro initialState i env state_var block_var state block blocks _ h_input h_holds spec_previous
    simp_all only [circuit_norm,
      AbsorbBlock.circuit, AbsorbBlock.Assumptions, AbsorbBlock.Spec,
      KeccakBlock.normalized, absorbBlocks]
    rw [List.concat_eq_append, List.map_append, List.map_cons, List.map_nil, List.foldl_concat]

  completeness := by
    simp_all only [InductiveTable.Completeness, circuit_norm, AbsorbBlock.circuit, KeccakBlock.normalized,
      AbsorbBlock.Assumptions, AbsorbBlock.Spec]

  outputFreshVars := by
    simp only [circuit_norm, KeccakBlock.normalized, AbsorbBlock.circuit,
      Permutation.stateVar, RATE]
    have h8 : size U64 = 8 := rfl
    apply @Var.outputFreshVars_of_isFreshVars _ _ (ProvableVector U64 25)
    apply Var.isFreshVars_provableVector
      (bases := fun j => if (0 : ℕ) = j.val
        then 25 * 8 + 17 * 8 + 136 + 23 * 1288 + 1280
        else 25 * 8 + 17 * 8 + 136 + 23 * 1288 + j.val * 16 + 888)
    · intro ⟨j, hj⟩
      simp only [Vector.getElem_set, Vector.getElem_mapRange]
      split <;> rfl
    · intro ⟨j, hj⟩; split <;> omega
    · intro ⟨j, hj⟩; simp only [h8]; split <;> omega
    · intro a b hab
      have hab_val : a.val ≠ b.val := fun h => hab (Fin.ext h)
      simp only [h8]
      split <;> rename_i h1 <;> split <;> rename_i h2
      · omega
      · right; omega
      · left; omega
      · rcases Nat.lt_or_gt_of_ne hab_val with h | h
        · left; omega
        · right; omega

-- the input is hard-coded to the initial keccak state of all zeros
def initialState : KeccakState (F p) := .fill 25 (U64.fromByte 0)

lemma initialState_value : (initialState (p:=p)).value = .fill 25 0 := by
  ext i hi
  simp only [initialState, KeccakState.value]
  rw [Vector.getElem_map, Vector.getElem_fill, Vector.getElem_fill, U64.fromByte_value, Fin.val_zero]

lemma initialState_normalized : (initialState (p:=p)).Normalized := by
  simp only [initialState, KeccakState.Normalized, Vector.getElem_fill, U64.fromByte_normalized]
  trivial

def formalTable (output : KeccakState (F p)) := table.toFormal initialState output

-- The table's statement implies that the output state is the result of keccak-hashing some list of input blocks
theorem tableStatement (output : KeccakState (F p)) : ∀ n > 0, ∀ trace env, ∃ blocks, blocks.length = n - 1 ∧
  (formalTable output).statement n trace env →
    output.Normalized ∧ output.value = absorbBlocks blocks := by
  intro n hn trace env
  use (InductiveTable.traceInputs trace.tail).map KeccakBlock.value
  intro Spec
  simp only [formalTable, FormalTable.statement, table, InductiveTable.toFormal] at Spec
  simp only [List.length_map, Trace.toList_length, trace.tail.prop, InductiveTable.traceInputs, hn] at Spec
  simp only [initialState_value, initialState_normalized, absorbBlocks, Specs.Keccak256.initialState, true_and] at Spec
  exact Spec rfl

end Tables.KeccakInductive
