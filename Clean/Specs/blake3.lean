import Clean.Utils.Bitwise

namespace Specs.blake3
open Bitwise (add32 rot_right32)
/--
CONSTANTS
-/

-- Default ouput length is 256 bits (32 bytes)
def outLen : Nat := 32

-- Default key length is 256 bits (32 bytes)
def keyLen : Nat := 32

/--
The number of input bytes in each block, i.e., 64 for all
blocks except the last block of the last chunk, which may be short.
-/
def blockLen : Nat := 64

/--
BLAKE3 splits its input into 1024-byte chunks and arranges them
as the leaves of a binary tree.
-/
def chunkLen : Nat := 1024

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
def chunkStart : Nat := 2^0
def chunkEnd : Nat := 2^1
def parent : Nat := 2^2
def root : Nat := 2^3
def keyedHash : Nat := 2^4
def deriveKeyContext : Nat := 2^5
def deriveKeyMaterial : Nat := 2^6

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
def msgPermutation : Vector Nat 16 :=
--   0  1  2   3  4  5  6   7  8   9  10 11 12  13  14 15
  #v[2, 6, 3, 10, 7, 0, 4, 13, 1, 11, 12, 5, 9, 14, 15, 8]

-- The mixing function, G, which mixes either a column or a diagonal.
def g(state: Vector Nat 16) (a b c d : Fin 16) (mx my : Nat) : Vector Nat 16 :=
  let state_a := add32 (state[a]) (add32 state[b] mx)
  let state_d := rot_right32 (state[d] ^^^ state_a) 16
  let state_c := add32 (state[c]) state_d
  let state_b := rot_right32 (state[b] ^^^ state_c) 12

  let state_a := add32 state_a (add32 state_b my)
  let state_d := rot_right32 (state_d ^^^ state_a) 8
  let state_c := add32 state_c state_d
  let state_b := rot_right32 (state_b ^^^ state_c) 7

  state.set a state_a
        |>.set b state_b
        |>.set c state_c
        |>.set d state_d


/--
TESTS


Test g function.
According to the reference (Python) implementation, the following should
yield the new state:
[3279123572, 367480655, 3947042124, 3663589532, 1286102396, 687960962, 441968613, 3595364146, 3111632159, 1102204962, 944689943, 3680149627, 3129663845, 3265095166, 606420953, 4183330326]
-/
def stateInit : Vector Nat 16 := #v[1321565287, 1539917118, 1918974978, 1109417770, 1286102396, 687960962, 441968613, 3595364146, 3111632159, 1102204962, 944689943, 3680149627, 3129663845, 3265095166, 606420953, 4183330326]
#eval g stateInit 0 1 2 3 4 5


end Specs.blake3
