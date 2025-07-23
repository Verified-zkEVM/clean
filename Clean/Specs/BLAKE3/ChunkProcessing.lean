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
-- With the fix, 64 bytes now stay in the buffer (matching Python behavior)
example :
    let state := initialChunkState testCV 0
    let updated := updateChunk state testBlock64
    updated.blocks_compressed = 0 ∧ updated.block_buffer = testBlock64 := by
  simp only [updateChunk, initialChunkState, testBlock64]
  simp only [List.nil_append]
  have h64 : (List.range 64).length = blockLen := by simp [List.length_range, blockLen]
  rw [splitIntoBlocks_exact _ h64]
  simp [processBlocks]

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
  simp only [List.nil_append, splitIntoBlocks]
  rw [splitIntoBlocks.go, blockLen, List.length_range]
  norm_num
  rw [splitIntoBlocks.go, blockLen, List.length_drop, List.length_range]
  norm_num
  decide

-- Test full chunk (1024 bytes = 16 blocks)
def testChunk1024 : List Nat := List.range 1024

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
  decide

-- Test vectors from Python reference implementation
-- These ensure our implementation matches the reference
--
-- Test vectors were generated using the pure Python BLAKE3 implementation from:
-- https://github.com/oconnor663/pure_python_blake3/blob/main/pure_blake3.py
--
-- The following Python code was used to generate these test vectors:
-- ```python
-- from pure_blake3 import *
--
-- def test_process_chunk(input_bytes, chunk_counter, flags):
--     chunk_state = ChunkState(IV, chunk_counter, flags)
--     chunk_state.update(input_bytes)
--     output = chunk_state.output()
--     cv = output.chaining_value()
--     return cv
--
-- # Generate test vectors with different inputs and parameters
-- cv = test_process_chunk(bytes([0x00]), 0, 0)  # One byte [0x00]
-- cv = test_process_chunk(bytes([0x01]), 0, 0)  # One byte [0x01]
-- cv = test_process_chunk(bytes([0x00]), 1, 0)  # Different chunk counter
-- cv = test_process_chunk(bytes([0x00]), 0, KEYED_HASH)  # With flag
-- cv = test_process_chunk(bytes(range(63)), 0, 0)  # 63 bytes (partial block)
-- cv = test_process_chunk(bytes(range(64)), 0, 0)  # Full block
-- cv = test_process_chunk(bytes(), 0, 0)  # Empty input
-- ```

-- Test: One byte [0x00], chunk_counter=0, flags=0
example :
    let input := [0x00]
    let cv := processChunk testCV 0 input 0
    cv = Vector.ofFn (fun i => [0x88a7f10d, 0x87d2711d, 0xfcc2afd0, 0x283dd2d7,
                                0x1a402ef1, 0x26ca58b8, 0xf1c5117f, 0x15f30d71][i.val]!) := by
  native_decide

-- Test: One byte [0x01], chunk_counter=0, flags=0
example :
    let input := [0x01]
    let cv := processChunk testCV 0 input 0
    cv = Vector.ofFn (fun i => [0xe0641a49, 0x861fb82d, 0xbc0a78ea, 0xb36c5459,
                                0x20b132ba, 0x844771de, 0x810eb14f, 0xa9f9aa83][i.val]!) := by
  native_decide

-- Test: One byte [0x00], chunk_counter=1, flags=0
example :
    let input := [0x00]
    let cv := processChunk testCV 1 input 0
    cv = Vector.ofFn (fun i => [0xb4a966bb, 0xef249a25, 0x44fb67fa, 0x41cc3d83,
                                0x19a2b2ef, 0xae303b45, 0xf9120052, 0xf667bfa9][i.val]!) := by
  native_decide

-- Test: One byte [0x00], chunk_counter=0, flags=KEYED_HASH
example :
    let input := [0x00]
    let cv := processChunk testCV 0 input keyedHash
    cv = Vector.ofFn (fun i => [0x493433a9, 0x78e5fe64, 0x3bbfefc4, 0x7dd1ac29,
                                0x9beae5b1, 0x31609733, 0x1a518b72, 0x626f54e0][i.val]!) := by
  native_decide

-- Test: 63 bytes [0x00, 0x01, ..., 0x3E], chunk_counter=0, flags=0
-- This tests a partial block (one byte short of a full block)
example :
    let input := List.range 63
    let cv := processChunk testCV 0 input 0
    cv = Vector.ofFn (fun i => [0xf6b8fdee, 0x34b20c2d, 0xa2164bd9, 0x26b77e83,
                                0x61880165, 0xef896a39, 0xfbd1289f, 0x24ca0f19][i.val]!) := by
  native_decide

-- Test: 64 bytes [0x00, 0x01, ..., 0x3F], chunk_counter=0, flags=0
example :
    let input := List.range 64
    let cv := processChunk testCV 0 input 0
    cv = Vector.ofFn (fun i => [0xc941de6d, 0xb0395ad0, 0x2066489b, 0x76cfc3f2,
                                0xf3e7fd52, 0x532341eb, 0x293457d9, 0x8e345d4c][i.val]!) := by
  native_decide

-- Test: Empty input [], chunk_counter=0, flags=0
example :
    let input : List Nat := []
    let cv := processChunk testCV 0 input 0
    cv = Vector.ofFn (fun i => [0x3c6b68b4, 0x4d3f958d, 0xbc515d18, 0xe6bcd79c,
                                0x762d78d9, 0x60c0f859, 0xffc3d468, 0x4168e5a6][i.val]!) := by
  native_decide

-- Test: 127 bytes (one byte short of 2 blocks)
-- 127 bytes [0x00, 0x01, ..., 0x7E], chunk_counter=0, flags=0
example :
    let input := List.range 127
    let cv := processChunk testCV 0 input 0
    cv = Vector.ofFn (fun i => [0x45c6fdcd, 0x24bb59bd, 0x8b25df15, 0xf0a1970d,
                                0x0f71687e, 0x1ee6e667, 0xf415aa78, 0xa2533d70][i.val]!) := by
  native_decide

-- Test: 128 bytes (exactly 2 blocks)
-- 128 bytes [0x00, 0x01, ..., 0x7F], chunk_counter=0, flags=0
example :
    let input := List.range 128
    let cv := processChunk testCV 0 input 0
    cv = Vector.ofFn (fun i => [0x8d4a1ad4, 0xdc39d407, 0x5af49238, 0x4f936b29,
                                0x66d9bb2f, 0x40869ff2, 0xdd158fe8, 0xc71500e2][i.val]!) := by
  native_decide

-- Test: 129 bytes (2 blocks + 1 byte)
-- 129 bytes [0x00, 0x01, ..., 0x80], chunk_counter=0, flags=0
example :
    let input := List.range 129
    let cv := processChunk testCV 0 input 0
    cv = Vector.ofFn (fun i => [0xd035027a, 0x10ed22b6, 0x9f5c3ac0, 0x6bb3cf7f,
                                0xfbaec82f, 0x5da9e350, 0x3edd8aed, 0x14621206][i.val]!) := by
  native_decide

-- Test: 256 bytes (exactly 4 blocks)
-- 256 bytes [0x00, 0x01, ..., 0xFF], chunk_counter=0, flags=0
example :
    let input := List.range 256
    let cv := processChunk testCV 0 input 0
    cv = Vector.ofFn (fun i => [0xcf9d0b74, 0x6ae5eab9, 0xafe9997d, 0x63185e2a,
                                0x2429193e, 0xea8836cf, 0x59bc2b40, 0x81fdfc97][i.val]!) := by
  native_decide

-- Test: 512 bytes (exactly 8 blocks)
-- 512 bytes [0x00, 0x01, ..., 0xFF, 0x00, 0x01, ..., 0xFF], chunk_counter=0, flags=0
example :
    let input := (List.range 512).map (· % 256)
    let cv := processChunk testCV 0 input 0
    cv = Vector.ofFn (fun i => [0xad2b8f62, 0x267c8093, 0x8ea5ebf2, 0xc2c1eded,
                                0xb4e7a6b7, 0x44ca9cf1, 0x20a09e2d, 0x4ede6cc6][i.val]!) := by
  native_decide

-- Test: 1023 bytes (one byte short of full chunk)
-- 1023 bytes [0x00, 0x01, ..., 0xFE], chunk_counter=0, flags=0
example :
    let input := (List.range 1023).map (· % 256)
    let cv := processChunk testCV 0 input 0
    cv = Vector.ofFn (fun i => [0x55c83635, 0xe92dd55a, 0xc19a6f2a, 0x52bb39df,
                                0x35e0db32, 0xf2ea92ee, 0x6e380d0f, 0x835aed33][i.val]!) := by
  native_decide

-- Test: 1024 bytes (full chunk)
-- 1024 bytes [0x00, 0x01, ..., 0xFF, 0x00, 0x01, ..., 0xFF], chunk_counter=0, flags=0
example :
    let input := (List.range 1024).map (· % 256)
    let cv := processChunk testCV 0 input 0
    cv = Vector.ofFn (fun i => [0x7f132571, 0xbd1932d6, 0xa2fa19bb, 0x2991bd74,
                                0xd7ac7427, 0xca0082a5, 0xc915e455, 0xeefa363f][i.val]!) := by
  native_decide

end Specs.BLAKE3.ChunkProcessing.Tests
