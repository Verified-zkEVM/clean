# BLAKE3 Chunk Processing: Lean vs Python Reference Comparison

## Overview
This document compares our Lean implementation with the pure Python BLAKE3 reference implementation.

## Key Similarities

### 1. Constants
Both implementations use the same constants:
- `BLOCK_LEN = 64` (bytes per block)
- `CHUNK_LEN = 1024` (bytes per chunk, which is 16 blocks)
- `CHUNK_START` and `CHUNK_END` flags

### 2. ChunkState Structure
**Python:**
```python
@dataclass
class ChunkState:
    chaining_value: list[int]      # 8 words
    chunk_counter: int
    block: bytearray               # Current block buffer
    block_len: int                 # Bytes in current block
    blocks_compressed: int         # Number of blocks processed
    flags: int
```

**Lean:**
```lean
structure ChunkState where
  chaining_value : Vector Nat 8      -- Current chaining value (8 × 32-bit words)
  chunk_counter : Nat                -- Which chunk number this is
  blocks_compressed : Nat            -- Number of blocks compressed so far
  block_buffer : List Nat            -- Current block bytes (0-63 bytes)
```

The structures are very similar, with the main difference being that Python stores `block_len` separately while Lean uses `block_buffer.length`.

### 3. Start Flag Logic
Both implementations set `CHUNK_START` flag only for the first block:

**Python:**
```python
def start_flag(self) -> int:
    if self.blocks_compressed == 0:
        return CHUNK_START
    else:
        return 0
```

**Lean:**
```lean
def startFlag (state : ChunkState) : Nat :=
  if state.blocks_compressed = 0 then chunkStart else 0
```

### 4. Update Logic
Both follow the same pattern:
1. Accumulate bytes in a buffer
2. When buffer reaches 64 bytes, compress it
3. Update chaining value and increment blocks_compressed
4. Clear buffer for next block

## Key Differences

### 1. Chunking Approach
**Python:** Processes bytes incrementally within ChunkState.update(), compressing blocks as they fill up.

**Lean:** We created a separate `splitIntoBlocks` function that splits input into blocks first, then processes them with `processBlocks`.

### 2. Tail Recursion
**Lean:** Uses tail-recursive `splitIntoBlocks.go` with an accumulator for efficiency.

**Python:** Uses imperative while loops.

### 3. Type System
**Lean:** Strong typing with `Vector Nat 8` for chaining values, ensuring compile-time size guarantees.

**Python:** Runtime typing with lists.

## Validation Points

Our Lean implementation correctly models the Python reference:
1. ✓ Same chunk and block sizes
2. ✓ Same flag handling (CHUNK_START only on first block)
3. ✓ Same state tracking (chaining value, counter, blocks compressed)
4. ✓ Same compression flow (accumulate → compress → update state)

## Test Coverage

Our tests validate:
- Empty chunk processing
- Single block (64 bytes)
- Partial block (65 bytes = 1 block + 1 byte remainder)
- Full chunk (1024 bytes = 16 blocks)
- Correct flag setting

These align with the core behaviors in the Python implementation.