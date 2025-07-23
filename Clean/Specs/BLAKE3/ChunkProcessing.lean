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
    else if bytes.length = blockLen then
      -- If we have exactly one block worth of bytes, keep them as remainder
      -- This matches Python's behavior where a full block at the end stays in buffer
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

-- Lemma: splitIntoBlocks with exact blockLen returns empty blocks and the list as remainder
-- This matches Python behavior where a full block at the end is kept for finalization
theorem splitIntoBlocks_exact (l : List Nat) (h : l.length = blockLen) :
    splitIntoBlocks l = ([], l) := by
  rw [splitIntoBlocks, splitIntoBlocks.go]
  have : ¬(l.length < blockLen) := by simp [h]
  simp [this, h]

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
