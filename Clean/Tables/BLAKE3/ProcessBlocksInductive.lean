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
import Clean.Gadgets.ConditionalU32
import Clean.Gadgets.ConditionalVector8U32
import Clean.Gadgets.IsZeroU32

namespace Tables.BLAKE3.ProcessBlocksInductive
open Gadgets
open Specs.BLAKE3

variable {p : ℕ} [Fact p.Prime] [p_large: Fact (p > 2^32)]
-- Add the additional constraint needed by Compress
instance : Fact (p > 2^16 + 2^8) := .mk (by
  cases p_large
  linarith
)

omit p_large in
lemma U32_one_is_Normalized (env : Environment (F p)) :
    (eval (α := U32) env { x0 := 1, x1 := 0, x2 := 0, x3 := 0 }).Normalized := by
  simp only [Parser.Attr.explicit_provable_type, ProvableType.eval, toVars, toElements]
  simp only [Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil]
  simp only [Expression.eval, fromElements, U32.Normalized]
  simp only [ZMod.val_zero, ZMod.val_one, Nat.ofNat_pos, and_self, and_true]
  omega

lemma U32_blockLen_is_Normalized (env : Environment (F p)) :
    (eval (α := U32) env { x0 := Expression.const ↑blockLen, x1 := 0, x2 := 0, x3 := 0 }).Normalized := by
  simp only [Parser.Attr.explicit_provable_type, ProvableType.eval, toVars, toElements]
  simp only [Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil]
  simp only [Expression.eval, fromElements, U32.Normalized]
  simp only [ZMod.val_zero, Nat.ofNat_pos, and_self, and_true]
  simp only [blockLen]
  cases p_large
  rw [ZMod.val_natCast_of_lt] <;> omega

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

/--
Input for each row: either a block to process or nothing.
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



/--
The step function that processes one block or passes through the state.
-/
def step (state : Var ProcessBlocksState (F p)) (input : Var BlockInput (F p)) :
    Circuit (F p) (Var ProcessBlocksState (F p)) := do

  -- Add constraint that block_exists is boolean
  input.block_exists * (input.block_exists - 1) === 0

  -- Compute CHUNK_START flag (1 if blocks_compressed = 0, else 0)
  let isFirstBlock ← IsZeroU32.circuit state.blocks_compressed
  let startFlagValue ← witness fun env => isFirstBlock.eval env * chunkStart
  let startFlagU32 : Var U32 (F p) := ⟨startFlagValue, 0, 0, 0⟩

  -- Prepare constants
  let zeroU32 : Var U32 (F p) := ⟨0, 0, 0, 0⟩
  let blockLenU32 : Var U32 (F p) := ⟨(blockLen : F p), 0, 0, 0⟩

  -- Prepare inputs for compress
  let compressInput : Var Gadgets.BLAKE3.ApplyRounds.Inputs (F p) := {
    chaining_value := state.chaining_value
    block_words := input.block_data
    counter_high := zeroU32
    counter_low := state.chunk_counter
    block_len := blockLenU32
    flags := startFlagU32
  }

  -- Apply compress to get new chaining value
  let newCV16 ← Gadgets.BLAKE3.Compress.circuit compressInput
  -- Take first 8 elements for the chaining value
  let newCV8 : Vector (U32 (Expression (F p))) 8 :=
    Vector.mk (newCV16.toArray.toList.take 8).toArray (by simp)

  -- Increment blocks_compressed
  let one32 : Var U32 (F p) := ⟨1, 0, 0, 0⟩
  let newBlocksCompressed ← Addition32.circuit { x := state.blocks_compressed, y := one32 }

  -- Create the new state (if block exists)
  let newState : Var ProcessBlocksState (F p) := {
    chaining_value := newCV8
    chunk_counter := state.chunk_counter
    blocks_compressed := newBlocksCompressed
  }

  -- Conditionally select between new state and old state based on block_exists
  -- If block_exists = 1, use newState; if block_exists = 0, use state
  let muxedCV ← ConditionalVector8U32.circuit {
    cond := input.block_exists
    ifTrue := newState.chaining_value
    ifFalse := state.chaining_value
  }

  let muxedBlocksCompressed ← do
    let condInput : Var Gadgets.ConditionalU32.Inputs (F p) := {
      cond := input.block_exists
      ifTrue := newBlocksCompressed
      ifFalse := state.blocks_compressed
    }
    Gadgets.ConditionalU32.circuit condInput

  return {
    chaining_value := muxedCV
    chunk_counter := state.chunk_counter  -- Never changes
    blocks_compressed := muxedBlocksCompressed
  }

/--
The InductiveTable for processBlocks.
-/
def table : InductiveTable (F p) ProcessBlocksState BlockInput where
  step

  Spec initialState inputs i _ state :=
    -- The spec relates the current state to the mathematical processBlocksWords function
    -- applied to the first i blocks from inputs (where block_exists = 1)
    let validBlocks := inputs.take i |>.filter (·.block_exists = 1)
    -- Extract the word data directly - no conversion needed!
    let blockWords := validBlocks.map (fun b => b.block_data.map (·.value))
    -- Use the initial state passed as parameter
    let finalState := processBlocksWords initialState.toChunkState blockWords
    -- Current state matches the result of processing all valid blocks so far
    state.toChunkState = finalState ∧
    state.Normalized

  InputAssumptions i input :=
    input.Normalized

  soundness := by
    intro initialState row_index env acc_var x_var acc x xs xs_len h_eval h_holds spec_previous
    sorry -- TODO: Prove soundness

  completeness := by
    intro initialState row_index env acc_var x_var acc x xs xs_len h_eval h_witnesses h_assumptions
    simp only [circuit_norm, step] at ⊢ h_witnesses
    provable_struct_simp
    simp only [h_eval] at ⊢ h_witnesses
    simp only [BlockInput.Normalized] at h_assumptions
    dsimp only [ProcessBlocksState.Normalized] at h_assumptions
    constructor
    · have : x_block_exists = 0 ∨ x_block_exists = 1 := by tauto
      cases this with
      | inl h =>
          simp only [h]
          ring_nf
      | inr h =>
          simp only [h]
          ring_nf
    constructor
    · simp only [IsZeroU32.circuit, IsZeroU32.Assumptions]
      simp_all
    constructor
    · simp only [BLAKE3.Compress.circuit, BLAKE3.Compress.Assumptions, BLAKE3.ApplyRounds.Assumptions]
      constructor
      · simp_all
      constructor
      · simp only [h_assumptions]
        native_decide
      constructor
      · -- goal looks lemma-worthy
        sorry
      constructor
      · simp_all
      constructor
      · -- goal looks lemma-worthy
        simp only [U32_blockLen_is_Normalized]
      -- why am I seeing 'var
/-           {
            index :=
              [8 * 4, 4, 4].sum + [1, 16 * 4].sum + ElaboratedCircuit.localLength field acc_var_blocks_compressed },
      x1 := 0, x2 := 0, x3 := 0 ' -/
      sorry
    constructor
    · dsimp only [Addition32.circuit, Addition32.Assumptions]
      constructor
      · simp only [h_assumptions]
      · simp only [U32_one_is_Normalized]
    constructor
    · dsimp only [ConditionalVector8U32.circuit]
      dsimp only [ConditionalVector8U32.Assumptions]
      simp_all
    dsimp only [ConditionalU32.circuit, ConditionalU32.Assumptions]
    simp_all

  subcircuitsConsistent := by
    intros
    dsimp only [step]
    simp only [circuit_norm]
    omega

/--
Create a trace for processBlocks with given input blocks.
Pads with empty blocks to reach exactly 17 rows.
-/
def createTrace (_initialCV : Vector (U32 (F p)) 8) (_chunkCounter : U32 (F p))
    (blocks : List (List Nat)) : List (BlockInput (F p)) :=
  -- Convert blocks to BlockInput format
  let blockInputs := blocks.map (fun block =>
    let words := (List.range 16).map (fun i =>
      let bytes := block.drop (i * 4) |>.take 4
      let value := bytes.zipIdx.foldl (fun acc (byte, idx) =>
        acc + byte * 256^idx
      ) 0
      U32.fromByte ⟨value % 256, by omega⟩  -- Simplified: just use first byte
    )
    { block_exists := 1
    , block_data := Vector.mk words.toArray (by
      simp only [List.length_map, List.length_range, List.size_toArray]
      rfl) }
  )
  -- Pad with empty blocks
  let emptyBlock : BlockInput (F p) :=
    { block_exists := 0
    , block_data := Vector.mk (List.replicate 16 (U32.fromByte 0)).toArray (by simp) }
  let paddedInputs := blockInputs ++ List.replicate (16 - blocks.length) emptyBlock
  paddedInputs

-- TODO: Define extractFinalState once we have the proper trace type
-- This would extract the final state from row 16 of the table

end Tables.BLAKE3.ProcessBlocksInductive
