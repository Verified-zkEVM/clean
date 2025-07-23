/- Simple Keccak example using `InductiveTable` -/
import Clean.Table.Inductive
import Clean.Circuit.Extensions
import Clean.Gadgets.Keccak.AbsorbBlock
import Clean.Specs.Keccak256
open Specs.Keccak256
variable {p : ℕ} [Fact p.Prime] [Fact (p > 2 ^ 16 + 2 ^ 8)]

namespace Tables.KeccakInductive
open Gadgets.Keccak256

def table : InductiveTable (F p) KeccakState KeccakBlock where
  step state block := do
    KeccakBlock.normalized block
    AbsorbBlock.circuit { state, block }

  Spec initialState blocks i _ state : Prop :=
    state.Normalized
    ∧ state.value = absorbBlocks (blocks.map KeccakBlock.value)

  InputAssumptions i block := block.Normalized

  soundness := by
    intro initialState i env state_var block_var state block blocks _ h_input h_holds spec_previous
    simp_all only [circuit_norm,
      AbsorbBlock.circuit, AbsorbBlock.Assumptions, AbsorbBlock.Spec,
      KeccakBlock.normalized, absorbBlocks]
    rw [List.concat_eq_append, List.map_append, List.map_cons, List.map_nil, List.foldl_concat]

  completeness := by
    intro initialState row_index env acc_var x_var acc x xs xs_len h_eval h_witnesses h_assumptions
    simp_all only [circuit_norm, AbsorbBlock.circuit, KeccakBlock.normalized,
      AbsorbBlock.Assumptions, AbsorbBlock.Spec, InitialStateAssumptions]

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
theorem tableStatement (output : KeccakState (F p)) : ∀ n > 0, ∀ trace, ∃ blocks, blocks.length = n - 1 ∧
  (formalTable output).statement n trace →
    output.Normalized ∧ output.value = absorbBlocks blocks := by
  intro n hn trace
  use (InductiveTable.traceInputs trace.tail).map KeccakBlock.value
  intro Spec
  simp only [formalTable, FormalTable.statement, table, InductiveTable.toFormal] at Spec
  simp only [List.length_map, Trace.toList_length, trace.tail.prop, InductiveTable.traceInputs, hn] at Spec
  simp only [initialState_value, initialState_normalized, absorbBlocks, Specs.Keccak256.initialState, true_and] at Spec
  exact Spec rfl

end Tables.KeccakInductive
