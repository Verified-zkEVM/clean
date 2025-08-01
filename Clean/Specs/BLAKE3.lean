import Clean.Utils.Bitwise

namespace Specs.BLAKE3

------------
-- CONSTANTS
------------

-- Default ouput length is 256 bits (32 bytes)
def outLen : ℕ := 32

-- Default key length is 256 bits (32 bytes)
def keyLen : ℕ := 32

/--
The number of input bytes in each block, i.e., 64 for all
blocks except the last block of the last chunk, which may be short.
-/
def blockLen : ℕ := 64

/--
BLAKE3 splits its input into 1024-byte chunks and arranges them
as the leaves of a binary tree.
-/
def chunkLen : ℕ := 1024

-- q Compression function doesn't seem to have an input 'd'.
-- Only the mixing function G has an input 'd'.
-- Was 'd' renamed to 'flags' in the reference implementation?
/--
The compression function input 'd' is a bitfield, with each
individual flag consisting of a power of 2. The value of 'd'
is the sum of all the flags defined for a given compression.
The following constants define their names and values:
(See Table 3 in the BLAKE3 paper.)
-/
def chunkStart : ℕ := 2^0
def chunkEnd : ℕ := 2^1
def parent : ℕ := 2^2
def root : ℕ := 2^3
def keyedHash : ℕ := 2^4
def deriveKeyContext : ℕ := 2^5
def deriveKeyMaterial : ℕ := 2^6

/--
The initialization constants for BLAKE3.
(Same as in BLAKE2s. See Table 1 in the BLAKE3 paper.)
-/
def iv : Vector UInt32 8 := #v[
  0x6a09e667,
  0xbb67ae85,
  0x3c6ef372,
  0xa54ff53a,
  0x510e527f,
  0x9b05688c,
  0x1f83d9ab,
  0x5be0cd19
]

/--
After each round (except the last one where it would be useless),
the message words are permuted according to the following
permutational key schedule for BLAKE3's keyed permutation.
(See Table 2 in the BLAKE3 paper.)
-/
def msgPermutation : Vector (Fin 16) 16 :=
--   0  1  2   3  4  5  6   7  8   9  10 11 12  13  14 15
  #v[2, 6, 3, 10, 7, 0, 4, 13, 1, 11, 12, 5, 9, 14, 15, 8]

------------
-- FUNCTIONS
------------

-- The mixing function, G, which mixes either a column or a diagonal.
def g (state: Vector ℕ 16) (a b c d : Fin 16) (mx my : ℕ) : Vector ℕ 16 :=
  let state_a := add32 (state[a]) (add32 state[b] mx)
  let state_d := rotRight32 (state[d] ^^^ state_a) 16
  let state_c := add32 (state[c]) state_d
  let state_b := rotRight32 (state[b] ^^^ state_c) 12

  let state_a := add32 state_a (add32 state_b my)
  let state_d := rotRight32 (state_d ^^^ state_a) 8
  let state_c := add32 state_c state_d
  let state_b := rotRight32 (state_b ^^^ state_c) 7

  state.set a state_a
        |>.set b state_b
        |>.set c state_c
        |>.set d state_d

/--
The constants a b c d for the G applications in the round, together with the indices
of the message words mx and my
-/
def roundConstants : Vector (Fin 16 × Fin 16 × Fin 16 × Fin 16 × Fin 16 × Fin 16) 8 := #v[
  (0, 4, 8, 12, 0, 1),
  (1, 5, 9, 13, 2, 3),
  (2, 6, 10, 14, 4, 5),
  (3, 7, 11, 15, 6, 7),
  (0, 5, 10, 15, 8, 9),
  (1, 6, 11, 12, 10, 11),
  (2, 7, 8, 13, 12, 13),
  (3, 4, 9, 14, 14, 15)
]

/--
The round function, which applies the mixing function G
to mix the state's columns and diagonals.
-/
def round (state: Vector ℕ 16) (m: Vector ℕ 16) : Vector ℕ 16 :=
  roundConstants.foldl (fun state (a, b, c, d, i, j) =>
    g state a b c d m[i] m[j]
  ) state

/--
The permutation function, which permutes the message words after each
round (except the last one where it would be useless).
-/
def permute (state: Vector ℕ 16) : Vector ℕ 16 :=
  Vector.ofFn (fun i => state[msgPermutation[i]])

/--
Apply a single round of mixing with optional message permutation.
Used in the fold operation for applying multiple rounds.
-/
def roundWithPermute (acc : Vector ℕ 16 × Vector ℕ 16) (round_num : ℕ) : Vector ℕ 16 × Vector ℕ 16 :=
  let (state, block_words) := acc
  let new_state := round state block_words
  -- Permute block words except for the last round (round 6, 0-indexed)
  let new_block_words := if round_num < 6 then permute block_words else block_words
  (new_state, new_block_words)

/--
Apply 7 rounds of mixing to the initialized state with message permutation.
Takes chaining value, block words, counter, block length, and flags,
initializes the state, and applies the rounds using foldl.
-/
def applyRounds (chaining_value: Vector ℕ 8) (block_words: Vector ℕ 16) (counter: ℕ) (block_len: ℕ) (flags: ℕ) : Vector ℕ 16 :=
  -- Split counter into low and high parts
  let counter_low := counter % 2^32
  let counter_high := counter / 2^32

  -- Initialize state with chaining value, IV, counter, block length and flags
  let state := #v[
    chaining_value[0], chaining_value[1], chaining_value[2], chaining_value[3],
    chaining_value[4], chaining_value[5], chaining_value[6], chaining_value[7],
    iv[0].toNat, iv[1].toNat, iv[2].toNat, iv[3].toNat,
    counter_low, counter_high, block_len, flags
  ]

  let state := round state block_words
  let block_words := permute block_words
  let state := round state block_words
  let block_words := permute block_words
  let state := round state block_words
  let block_words := permute block_words
  let state := round state block_words
  let block_words := permute block_words
  let state := round state block_words
  let block_words := permute block_words
  let state := round state block_words
  let block_words := permute block_words
  let state := round state block_words

  state

/--
Final state update that XORs the first 8 words with the last 8 words,
and the last 8 words with the original chaining value.
-/
def finalStateUpdate (state: Vector ℕ 16) (chaining_value: Vector ℕ 8) : Vector ℕ 16 :=
  #v[
    state[0] ^^^ state[8],
    state[1] ^^^ state[9],
    state[2] ^^^ state[10],
    state[3] ^^^ state[11],
    state[4] ^^^ state[12],
    state[5] ^^^ state[13],
    state[6] ^^^ state[14],
    state[7] ^^^ state[15],
    chaining_value[0] ^^^ state[8],
    chaining_value[1] ^^^ state[9],
    chaining_value[2] ^^^ state[10],
    chaining_value[3] ^^^ state[11],
    chaining_value[4] ^^^ state[12],
    chaining_value[5] ^^^ state[13],
    chaining_value[6] ^^^ state[14],
    chaining_value[7] ^^^ state[15]
  ]

/--
The compression function, which takes a chaining value, block words, counter,
block length, and flags as input and produces a new state vector.
This is the core function of BLAKE3.
-/
def compress (chaining_value: Vector ℕ 8) (block_words: Vector ℕ 16) (counter: ℕ) (block_len: ℕ) (flags: ℕ) : Vector ℕ 16 :=
  let state := applyRounds chaining_value block_words counter block_len flags
  finalStateUpdate state chaining_value

--------
-- CHUNK PROCESSING
--------

/--
State maintained during chunk processing.
Tracks the current chaining value, number of blocks compressed,
and any partial block data.
-/
structure ChunkState where
  chaining_value : Vector ℕ 8      -- Current chaining value (8 × 32-bit words)
  chunk_counter : ℕ                -- Which chunk number this is
  blocks_compressed : ℕ            -- Number of blocks compressed so far
  block_buffer : List ℕ            -- Current block bytes (0-63 bytes)

/--
Initial chunk state with given chaining value and chunk counter.
-/
def initialChunkState (cv : Vector ℕ 8) (counter : ℕ) : ChunkState :=
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
def bytesToWords (bytes : List ℕ) : Vector ℕ 16 :=
  let paddedBytes : List ℕ := bytes ++ List.replicate (64 - bytes.length) 0
  have : 64 ≤ paddedBytes.length := by
    simp only [paddedBytes, List.length_append, List.length_replicate]
    omega
  Vector.ofFn fun (i : Fin 16) =>
    let byteIdx := i.val * 4
    paddedBytes[byteIdx] +
    paddedBytes[byteIdx + 1] * 256 +
    paddedBytes[byteIdx + 2] * 256^2 +
    paddedBytes[byteIdx + 3] * 256^3

/--
Determine if CHUNK_START flag should be set based on blocks compressed.
-/
def startFlag (state : ChunkState) : ℕ :=
  if state.blocks_compressed = 0 then chunkStart else 0

------------
-- Core Processing Functions
------------

/--
Process a single block given as 16 words, updating the chunk state.
This avoids the bytes-to-words conversion when the data is already in word format.
-/
def processBlockWords (state : ChunkState) (block_words : Vector ℕ 16) : ChunkState :=
  let flags := startFlag state
  let new_cv := compress state.chaining_value block_words state.chunk_counter blockLen flags
  { state with
    chaining_value := new_cv.take 8
    blocks_compressed := state.blocks_compressed + 1
    block_buffer := []
  }

/--
Split a list of bytes into complete blocks as words and a remainder.
Returns (complete_blocks_as_words, remainder_bytes).
Each block is returned as a Vector of 16 words.
-/
def splitIntoBlockWords (bytes : List ℕ) : (List (Vector ℕ 16) × List ℕ) :=
  splitIntoBlockWords.go bytes []
where
  /-- Tail-recursive helper function -/
  go (bytes : List ℕ) (acc : List (Vector ℕ 16)) : (List (Vector ℕ 16) × List ℕ) :=
    if bytes.length <= blockLen then
      -- If we have exactly one block worth of bytes, keep them as remainder
      -- This matches Python's behavior where a full block at the end stays in buffer
      (acc.reverse, bytes)
    else
      let blockBytes := bytes.take blockLen
      let blockWords := bytesToWords blockBytes
      let rest := bytes.drop blockLen
      go rest (blockWords :: acc)
  termination_by bytes.length
  decreasing_by
    simp only [List.length_drop, blockLen] at *
    omega

/--
Process a list of blocks given as words, updating the chunk state.
Each block is 16 words (64 bytes).
-/
def processBlocksWords (state : ChunkState) (blocks : List (Vector ℕ 16)) : ChunkState :=
  blocks.foldl processBlockWords state

/--
Main function for incremental chunk processing.
Accumulates input bytes and compresses full blocks.
-/
def updateChunk (state : ChunkState) (input_bytes : List ℕ) : ChunkState :=
  let combined := state.block_buffer ++ input_bytes
  let (blockWords, remainder) := splitIntoBlockWords combined
  let newState := processBlocksWords state blockWords
  { newState with block_buffer := remainder }

/--
Process the final block of a chunk with CHUNK_END flag.
Returns the final chaining value.
-/
def finalizeChunk (state : ChunkState) (base_flags : ℕ) : Vector ℕ 8 :=
  let block_words := bytesToWords state.block_buffer
  let flags := base_flags ||| startFlag state ||| chunkEnd
  let final_state := compress state.chaining_value block_words state.chunk_counter state.block_buffer.length flags
  final_state.take 8

/--
Process a complete chunk from start to finish.
-/
def processChunk (cv : Vector ℕ 8) (chunk_counter : ℕ) (chunk_bytes : List ℕ) (base_flags : ℕ) : Vector ℕ 8 :=
  let initial := initialChunkState cv chunk_counter
  let updated := updateChunk initial chunk_bytes
  finalizeChunk updated base_flags

end Specs.BLAKE3

--------
-- TESTS
--------

namespace Specs.BLAKE3.Tests

/--
The following checks are based on the reference Python implementation of BLAKE3:
https://github.com/oconnor663/pure_python_blake3/blob/main/pure_blake3.py
-/

-- Test g function.
def stateInitG : Vector ℕ 16 := #v[1321565287, 1539917118, 1918974978, 1109417770, 1286102396, 687960962, 441968613, 3595364146, 3111632159, 1102204962, 944689943, 3680149627, 3129663845, 3265095166, 606420953, 4183330326]
example : g stateInitG 0 1 2 3 4 5 = #v[3279123572, 367480655, 3947042124, 3663589532, 1286102396, 687960962, 441968613, 3595364146, 3111632159, 1102204962, 944689943, 3680149627, 3129663845, 3265095166, 606420953, 4183330326] := rfl

-- Test round function.
def stateInitRound : Vector ℕ 16 := #v[1048429017, 869689525, 3373747814, 3881173978, 867318181, 93804160, 1095841330, 3806666906, 1528071400, 2951122214, 4271188711, 3509256835, 40453064, 3578515354, 1456976626, 243768026]
def m : Vector ℕ 16 := #v[3959934058, 3329161910, 3688806782, 3025089236, 897128991, 1111177342, 4132823147, 2420086736, 1951041921, 2483382132, 1478626316, 2397174491, 1858261849, 1494602388, 4275385857, 3719915132]
example : round stateInitRound m = #v[2183394319, 368400627, 2705018986, 1532359963, 184541119, 4093912516, 344508834, 154001542, 2580533130, 866577463, 1629990543, 2086044263, 618301763, 3154665623, 3243728413, 699478374] := rfl

-- Test permutation function.
def stateInitPermute : Vector ℕ 16 := #v[3383581781, 3743774256, 2003572531, 1426274751, 826242452, 1591270934, 3844308220, 2585707362, 2245261223, 142878727, 3284326898, 338750343, 4278730886, 3963897632, 4264855050, 15597940]
example : permute stateInitPermute = #v[2003572531, 3844308220, 1426274751, 3284326898, 2585707362, 3383581781, 826242452, 3963897632, 3743774256, 338750343, 4278730886, 1591270934, 142878727, 4264855050, 15597940, 2245261223] := rfl

-- Test compress function.
def chainingValue : Vector ℕ 8 := #v[671114869, 2251103971, 1125212539, 2996205183, 1286164105, 2483632496, 367841012, 3199388477]
def blockWords : Vector ℕ 16 := #v[1260152445, 449952550, 2837099038, 716667674, 3544843723, 387900774, 3257147430, 2088822348, 4202301432, 2249467574, 1521610824, 186847680, 2726995727, 3572868764, 1936257617, 3338044720]
def counter : ℕ := 953581910
def blockLen : ℕ := 2437728858
def flags : ℕ := 2498436276
-- Necessary to avoid 'maximum recursion depth has been reached' error during 'rfl'.
set_option maxRecDepth 800
example : compress chainingValue blockWords counter blockLen flags = #v[2723421452, 2900812491, 409287158, 2844031487, 1256578214, 2677699013, 2070649829, 3853882973, 2869165109, 1080268436, 1942754410, 576800287, 963977849, 584425189, 1029827681, 3685994844] := rfl

end Specs.BLAKE3.Tests
