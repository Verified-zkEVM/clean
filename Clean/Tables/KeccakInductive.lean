/- Simple Keccak example using `InductiveTable` -/
import Clean.Table.Inductive
import Clean.Circuit.Extensions
import Clean.Gadgets.Keccak.AbsorbBlock
import Clean.Specs.Keccak256
open Specs.Keccak256
variable {p : ℕ} [Fact p.Prime] [Fact (p > 2 ^ 16 + 2 ^ 8)]

namespace Tables.KeccakInductive
open Gadgets.Keccak256

set_option trace.Meta.Tactic.simp true

def table : InductiveTable (F p) KeccakState where
  step state := do
    let block : KeccakBlock (Expression (F p)) ← ProvableType.witnessAny KeccakBlock
    assertion KeccakBlock.normalized block
    subcircuit AbsorbBlock.circuit { state, block }

  spec i state : Prop :=
    state.is_normalized
    ∧ ∃ blocks : List (Vector ℕ RATE), blocks.length = i
      ∧ state.value = absorb_blocks blocks

  soundness := by
    intro i env state_var state h_input h_holds spec_previous
    simp_all only [circuit_norm, subcircuit_norm,
      AbsorbBlock.circuit, AbsorbBlock.assumptions, AbsorbBlock.spec,
      KeccakBlock.normalized]
    replace h_holds := h_holds.right h_holds.left
    set block := (eval env (var_from_offset KeccakBlock (25 * 8))).value
    obtain ⟨ blocks, blocks_length, state_value ⟩ := spec_previous.right
    use blocks.concat block
    constructor
    · rw [List.length_concat, blocks_length]
    rw [state_value]
    simp only [absorb_blocks]
    rw [List.concat_eq_append, List.foldl_concat]

  completeness := by
    intro i env state_var state h_input h_env spec_previous
    set block' := ProvableType.witnessAny (F:=F p) KeccakBlock
    simp_all only [circuit_norm, subcircuit_norm,
      AbsorbBlock.circuit, AbsorbBlock.assumptions, AbsorbBlock.spec,
      KeccakBlock.normalized]
    set block := (block' (25 * 8)).1
    simp only [block'] at h_env ⊢
    simp only [circuit_norm] at h_env ⊢

end Tables.KeccakInductive
