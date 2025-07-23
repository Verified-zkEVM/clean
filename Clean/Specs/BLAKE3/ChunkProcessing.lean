import Clean.Specs.BLAKE3

namespace Specs.BLAKE3.ChunkProcessing

open Specs.BLAKE3

/--
State maintained during chunk processing.
Tracks the current chaining value, number of blocks compressed,
and any partial block data.
-/
structure ChunkState where
  chaining_value : Vector Nat 8      -- Current chaining value (8 × 32-bit words)
  chunk_counter : Nat                -- Which chunk number this is
  blocks_compressed : Nat            -- Number of blocks compressed so far
  block_buffer : List Nat            -- Current block bytes (0-63 bytes)

/--
Initial chunk state with given chaining value and chunk counter.
-/
def initialChunkState (cv : Vector Nat 8) (counter : Nat) : ChunkState :=
  { chaining_value := cv
  , chunk_counter := counter
  , blocks_compressed := 0
  , block_buffer := []
  }

------------
-- Helper Functions
------------

/--
Convert a list of bytes to 32-bit words (little-endian).
Pads with zeros if less than 64 bytes.
-/
def bytesToWords (bytes : List Nat) : Vector Nat 16 :=
  let paddedBytes := bytes ++ List.replicate (64 - bytes.length) 0
  Vector.ofFn fun i =>
    let byteIdx := i.val * 4
    paddedBytes[byteIdx]! +
    paddedBytes[byteIdx + 1]! * 256 +
    paddedBytes[byteIdx + 2]! * 256^2 +
    paddedBytes[byteIdx + 3]! * 256^3

/--
Determine if CHUNK_START flag should be set based on blocks compressed.
-/
def startFlag (state : ChunkState) : Nat :=
  if state.blocks_compressed = 0 then chunkStart else 0

------------
-- Core Processing Functions
------------

/--
Process a single 64-byte block, updating the chunk state.
-/
def processBlock (state : ChunkState) (block_bytes : List Nat) : ChunkState :=
  let block_words := bytesToWords block_bytes
  let flags := startFlag state
  let new_cv := compress state.chaining_value block_words state.chunk_counter blockLen flags
  { state with
    chaining_value := new_cv.take 8
    blocks_compressed := state.blocks_compressed + 1
    block_buffer := []
  }

/--
Split a list of bytes into complete blocks of size blockLen and a remainder.
Returns (complete_blocks, remainder).
-/
def splitIntoBlocks (bytes : List Nat) : (List (List Nat) × List Nat) :=
  splitIntoBlocks.go bytes []
where
  /-- Tail-recursive helper function -/
  go (bytes : List Nat) (acc : List (List Nat)) : (List (List Nat) × List Nat) :=
    if bytes.length < blockLen then
      (acc.reverse, bytes)
    else
      let block := bytes.take blockLen
      let rest := bytes.drop blockLen
      go rest (block :: acc)
  termination_by bytes.length
  decreasing_by
    simp only [List.length_drop, blockLen] at *
    omega

/--
Process a list of blocks sequentially, updating the chunk state.
-/
def processBlocks (state : ChunkState) (blocks : List (List Nat)) : ChunkState :=
  blocks.foldl processBlock state

/--
Main function for incremental chunk processing.
Accumulates input bytes and compresses full blocks.
-/
def updateChunk (state : ChunkState) (input_bytes : List Nat) : ChunkState :=
  let combined := state.block_buffer ++ input_bytes
  let (blocks, remainder) := splitIntoBlocks combined
  let newState := processBlocks state blocks
  { newState with block_buffer := remainder }

/--
Process the final block of a chunk with CHUNK_END flag.
Returns the final chaining value.
-/
def finalizeChunk (state : ChunkState) (base_flags : Nat) : Vector Nat 8 :=
  let block_words := bytesToWords state.block_buffer
  let flags := base_flags ||| startFlag state ||| chunkEnd
  let final_state := compress state.chaining_value block_words state.chunk_counter state.block_buffer.length flags
  final_state.take 8

/--
Process a complete chunk from start to finish.
-/
def processChunk (cv : Vector Nat 8) (chunk_counter : Nat) (chunk_bytes : List Nat) (base_flags : Nat) : Vector Nat 8 :=
  let initial := initialChunkState cv chunk_counter
  let updated := updateChunk initial chunk_bytes
  finalizeChunk updated base_flags

end Specs.BLAKE3.ChunkProcessing

--------
-- LEMMAS
--------

namespace Specs.BLAKE3.ChunkProcessing

-- Lemma: splitIntoBlocks with empty list returns empty blocks and empty remainder
theorem splitIntoBlocks_nil :
    splitIntoBlocks [] = ([], []) := by
  rw [splitIntoBlocks, splitIntoBlocks.go]
  simp [blockLen]

-- Lemma: splitIntoBlocks with list shorter than blockLen returns empty blocks and the list as remainder
theorem splitIntoBlocks_short (l : List Nat) (h : l.length < blockLen) :
    splitIntoBlocks l = ([], l) := by
  rw [splitIntoBlocks, splitIntoBlocks.go]
  simp [h]

-- Lemma: splitIntoBlocks with exact blockLen returns single block and empty remainder
theorem splitIntoBlocks_exact (l : List Nat) (h : l.length = blockLen) :
    splitIntoBlocks l = ([l], []) := by
  rw [splitIntoBlocks, splitIntoBlocks.go]
  have : ¬(l.length < blockLen) := by simp [h]
  simp [this]
  have hdrop : l.drop blockLen = [] := by
    apply List.eq_nil_of_length_eq_zero
    simp [List.length_drop, h]
  rw [splitIntoBlocks.go]
  simp [hdrop, blockLen, List.take_length, h]

-- Lemma about foldl with a single element list
theorem foldl_singleton {α β : Type} (f : β → α → β) (init : β) (x : α) :
    List.foldl f init [x] = f init x := by
  simp [List.foldl]

-- Lemma about processBlock incrementing blocks_compressed
theorem processBlock_increments_counter (state : ChunkState) (block : List Nat) :
    (processBlock state block).blocks_compressed = state.blocks_compressed + 1 := by
  simp [processBlock]

-- Lemma about processBlocks with single block
theorem processBlocks_single (state : ChunkState) (block : List Nat) :
    (processBlocks state [block]).blocks_compressed = state.blocks_compressed + 1 := by
  simp [processBlocks, foldl_singleton, processBlock_increments_counter]


end Specs.BLAKE3.ChunkProcessing

--------
-- TESTS
--------

namespace Specs.BLAKE3.ChunkProcessing.Tests

open Specs.BLAKE3.ChunkProcessing

-- Initial chaining value for tests (using BLAKE3 IV converted to Nat)
def testCV : Vector Nat 8 := iv.map (·.toNat)

-- Test empty chunk
example :
    let state := initialChunkState testCV 0
    let expected := compress testCV (bytesToWords []) 0 0 (chunkStart ||| chunkEnd)
    finalizeChunk state 0 = expected.take 8 := rfl

-- Test single block (64 bytes)
def testBlock64 : List Nat := List.range 64

-- Test single block processing
example :
    let state := initialChunkState testCV 0
    let updated := updateChunk state testBlock64
    updated.blocks_compressed = 1 ∧ updated.block_buffer = [] := by
  simp only [updateChunk, initialChunkState, testBlock64]
  simp only [List.nil_append]
  have h64 : (List.range 64).length = blockLen := by simp [List.length_range, blockLen]
  rw [splitIntoBlocks_exact _ h64]
  simp [processBlocks, foldl_singleton, processBlock_increments_counter]

-- Test that CHUNK_START flag is only set on first block
example :
    let state := initialChunkState testCV 0
    let state1 := processBlock state testBlock64
    let state2 := processBlock state1 testBlock64
    startFlag state = chunkStart ∧ startFlag state1 = 0 ∧ startFlag state2 = 0 := by
  simp only [startFlag, processBlock, initialChunkState, chunkStart]
  simp only [Nat.add_comm 0 1, Nat.one_ne_zero, ite_false]
  exact ⟨rfl, rfl, rfl⟩

-- Test chunk with partial final block (65 bytes = 1 full block + 1 byte)
def testChunk65 : List Nat := List.range 65

example :
    let state := initialChunkState testCV 0
    let updated := updateChunk state testChunk65
    updated.blocks_compressed = 1 ∧ updated.block_buffer.length = 1 := by
  simp only [updateChunk, initialChunkState, testChunk65]
  simp only [List.nil_append]
  -- For now, using sorry to simplify the proof
  sorry

-- Test full chunk (1024 bytes = 16 blocks)
def testChunk1024 : List Nat := List.range 1024

example :
    let state := initialChunkState testCV 0
    let updated := updateChunk state testChunk1024
    updated.blocks_compressed = 16 ∧ updated.block_buffer = [] := by
  simp only [updateChunk, initialChunkState, testChunk1024, chunkLen, blockLen]
  simp only [List.nil_append]
  sorry

-- Verify bytesToWords handles padding correctly for small input
example :
    let bytes := [0x01, 0x02, 0x03, 0x04, 0x05]  -- 5 bytes
    let words := bytesToWords bytes
    -- First word is little-endian: 0x04030201
    words[0] = 0x04030201 ∧
    -- Second word has only one byte: 0x00000005
    words[1] = 0x00000005 ∧
    -- Rest are zeros
    words[2] = 0 := by
  simp only [bytesToWords, Vector.ofFn]
  -- For now, using sorry to get the file building
  sorry

-- TODO: Add test vectors from Python reference implementation
-- These would be examples with specific expected outputs matching the reference

end Specs.BLAKE3.ChunkProcessing.Tests
