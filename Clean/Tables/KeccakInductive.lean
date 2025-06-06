/- Simple Keccak example using `InductiveTable` -/
import Clean.Table.Inductive
import Clean.Circuit.Extensions
import Clean.Gadgets.Keccak.AbsorbBlock
import Clean.Specs.Keccak256
open Specs.Keccak256

namespace Tables.KeccakInductive
open Gadgets.Keccak256
variable {p : ℕ} [Fact p.Prime] [Fact (p > 2 ^ 16 + 2 ^ 8)]

def table : InductiveTable (F p) KeccakState where
  step state := do
    let block ← ProvableVector.witnessAny U64 RATE
    subcircuit AbsorbBlock.circuit { state, block }

  spec i state : Prop :=
    state.is_normalized
    ∧ ∃ blocks : List (Vector ℕ RATE), blocks.length = i
      ∧ state.value = absorb_blocks blocks

  soundness := by sorry

  completeness := by sorry

end Tables.KeccakInductive
