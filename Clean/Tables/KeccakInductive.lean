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

end Tables.KeccakInductive
