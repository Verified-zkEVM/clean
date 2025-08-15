/-
InductiveTable implementation for BLAKE3's processBlocks function.
This table has exactly 17 rows:
- Rows 0-15: Process up to 16 blocks (64 bytes each)
- Row 16: Final output containing the result of processBlocks
-/
import Clean.Table.Inductive
import Clean.Gadgets.BLAKE3.Compress
import Clean.Specs.BLAKE3
import Clean.Gadgets.Addition32.Addition32
import Clean.Gadgets.Conditional
import Clean.Gadgets.IsZero

namespace Tables.BLAKE3.ProcessBlocksInductive
open Gadgets
open Specs.BLAKE3

section
variable {p : ℕ} [Fact p.Prime] [p_large: Fact (p > 2^32)]
-- Add the additional constraint needed by Compress
instance : Fact (p > 2^16 + 2^8) := .mk (by
  cases p_large
  linarith
)

private lemma ZMod_val_64 :
    ZMod.val (n:=p) 64 = 64 := by
  rw [ZMod.val_ofNat_of_lt]
  have := p_large.elim
  linarith

attribute [local circuit_norm] blockLen ZMod.val_zero ZMod.val_one ZMod_val_64 -- only in the current section

/--
State maintained during block processing.
Corresponds to a simplified version of ChunkState.
-/
structure ProcessBlocksState (F : Type) where
  chaining_value : Vector (U32 F) 8    -- Current chaining value (8 × 32-bit words)
  chunk_counter : U32 F                 -- Which chunk number this is
  blocks_compressed : U32 F             -- Number of blocks compressed so far

instance : ProvableStruct ProcessBlocksState where
  components := [ProvableVector U32 8, U32, U32]
  toComponents := fun { chaining_value, chunk_counter, blocks_compressed } =>
    .cons chaining_value (.cons chunk_counter (.cons blocks_compressed .nil))
  fromComponents := fun xss =>
    match xss with
    | .cons cv (.cons cc (.cons bc .nil)) =>
      { chaining_value := cv, chunk_counter := cc, blocks_compressed := bc }
  fromComponents_toComponents := by
    intros
    rfl

/--
Convert ProcessBlocksState to ChunkState for integration with the spec.
-/
def ProcessBlocksState.toChunkState (state : ProcessBlocksState (F p)) : ChunkState :=
  { chaining_value := state.chaining_value.map (·.value)
  , chunk_counter := state.chunk_counter.value
  , blocks_compressed := state.blocks_compressed.value
  , block_buffer := []  -- ProcessBlocksState doesn't track partial blocks
  }

/--
Predicate that all components of ProcessBlocksState are normalized (valid U32 values).
-/
def ProcessBlocksState.Normalized (state : ProcessBlocksState (F p)) : Prop :=
  (∀ i : Fin 8, state.chaining_value[i].Normalized) ∧
  state.chunk_counter.Normalized ∧
  state.blocks_compressed.Normalized

end
end Tables.BLAKE3.ProcessBlocksInductive
