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

omit p_large in
private lemma eval_acc_blocks_compressed (env : Environment (F p)) acc_chaining_value acc_chunk_counter acc_var_blocks_compressed
    acc_blocks_compressed
    (h_iszero : Expression.eval env (IsZero.circuit.elaborated.output acc_var_blocks_compressed 105) =
      if acc_blocks_compressed.value = 0 then 1 else 0) :
    eval env acc_var_blocks_compressed = acc_blocks_compressed →
    ProcessBlocksState.Normalized
      { chaining_value := acc_chaining_value, chunk_counter := acc_chunk_counter,
        blocks_compressed := acc_blocks_compressed } →
    (eval env
            (U32.mk
                (Expression.mul (IsZero.circuit.elaborated.output acc_var_blocks_compressed 105) (Expression.const ↑chunkStart))
                0 0 0 )).value =
    if acc_blocks_compressed.value = 0 then chunkStart else 0 := by
  intros h_eval h_normalized
  simp only [explicit_provable_type, circuit_norm, fromElements, toVars, toElements]
  simp only [ProcessBlocksState.Normalized] at h_normalized
  simp only [Expression.eval, chunkStart, h_iszero]
  split
  · simp only [U32.value]
    norm_num
    simp only [circuit_norm]
  · simp only [U32.value]
    norm_num

/--
Input for each row: either a block to process or nothing.
A chunk might contain less than 16 blocks, and `block_exists` indicates empty rows.
-/
structure BlockInput (F : Type) where
  block_exists : F                      -- 0 or 1 (boolean flag)
  block_data : Vector (U32 F) 16        -- 16 words = 64 bytes when exists

instance : ProvableStruct BlockInput where
  components := [field, ProvableVector U32 16]
  toComponents := fun { block_exists, block_data } =>
    .cons block_exists (.cons block_data .nil)
  fromComponents := fun xss =>
    match xss with
    | .cons block_exists (.cons data .nil) =>
      { block_exists := block_exists, block_data := data }
  fromComponents_toComponents := by
    intros
    rfl

/--
Predicate that all components of BlockInput are well-formed.
-/
def BlockInput.Normalized (input : BlockInput (F p)) : Prop :=
  (input.block_exists = 0 ∨ input.block_exists = 1) ∧
  (∀ i : Fin 16, input.block_data[i].Normalized)

end
end Tables.BLAKE3.ProcessBlocksInductive
