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
    assertion KeccakBlock.normalized block
    subcircuit AbsorbBlock.circuit { state, block }

  spec i state : Prop :=
    state.is_normalized
    ∧ ∃ blocks : List (KeccakBlock (F p)), blocks.length = i
      ∧ state.value = absorb_blocks (blocks.map KeccakBlock.value)

  input_spec i block := block.is_normalized

  soundness := by
    intro i env state_var block_var state block h_input h_holds spec_previous
    simp_all only [circuit_norm, subcircuit_norm,
      AbsorbBlock.circuit, AbsorbBlock.assumptions, AbsorbBlock.spec,
      KeccakBlock.normalized]
    replace h_holds := h_holds.right h_holds.left
    obtain ⟨ blocks, blocks_length, state_value ⟩ := spec_previous.right
    use blocks.concat block
    constructor
    · rw [List.length_concat, blocks_length]
    rw [state_value]
    simp only [absorb_blocks]
    rw [List.concat_eq_append, List.map_append, List.map_cons, List.map_nil, List.foldl_concat]

  completeness := by
    simp_all only [circuit_norm, AbsorbBlock.circuit, KeccakBlock.normalized,
      subcircuit_norm, AbsorbBlock.assumptions, AbsorbBlock.spec]

-- the input is hard-coded to the initial keccak state of all zeros
def initialState : KeccakState (F p) := .fill 25 (U64.from_byte 0)

lemma initialState_value : (initialState (p:=p)).value = .fill 25 0 := by
  ext i hi
  simp only [initialState, KeccakState.value]
  rw [Vector.getElem_map, Vector.getElem_fill, Vector.getElem_fill, U64.from_byte_value, Fin.val_zero]

lemma initialState_normalized : (initialState (p:=p)).is_normalized := by
  simp only [initialState, KeccakState.is_normalized, Vector.getElem_fill, U64.from_byte_is_normalized]
  trivial

def formalTable (output : KeccakState (F p)) := table.toFormal initialState output

def domain {p q : Sort*} (_ : p → q) := p

-- The table's statement implies that the output state is the result of keccak-hashing some list of input blocks
theorem tableStatement (output : KeccakState (F p)) : ∀ n > 0, ∀ trace,
  (formalTable output).statement n trace →
    output.is_normalized ∧
    ∃ blocks, blocks.length = n - 1
      ∧ output.value = absorb_blocks blocks := by
  intro n hn trace spec
  simp only [formalTable, FormalTable.statement, table, InductiveTable.toFormal, hn] at spec
  simp only [initialState_value, initialState_normalized, absorb_blocks, initial_state, true_and] at spec
  have ⟨ norm, ⟨ blocks, block_len, value_eq ⟩ ⟩ := spec ⟨ [], rfl, rfl ⟩
  clear spec
  use norm, blocks.map KeccakBlock.value
  simp only [List.length_map]
  exact ⟨ block_len, value_eq ⟩

end Tables.KeccakInductive
