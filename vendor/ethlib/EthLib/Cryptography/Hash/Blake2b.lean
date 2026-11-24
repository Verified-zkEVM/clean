module

/-!
# `Hash.Blake2b`

The compression function F of BLAKE2b, [RFC 7693](https://www.rfc-editor.org/rfc/rfc7693) §3.2.

BLAKE2b runs F once per 128-byte block, with 12 rounds (§3.3).

The BLAKE2F precompile lets the caller choose the number of rounds, so here it is an argument.

Each step of the RFC is one definition:

- the initialization vector, §2.6;
- the message schedule, §2.7;
- the rotation of a word, §2.3;
- the mixing function G, §3.1;
- one round of F, and F itself, §3.2.

The code is a direct transcription of the RFC, not a constant-time implementation.
-/

@[expose] public section

namespace EthLib.Cryptography.Hash.Blake2b

/-! ## Parameters

RFC 7693 §2.1 fixes the parameters of BLAKE2b:

- a word has `w = 64` bits;
- F runs `r = 12` rounds;
- G rotates by `(R1, R2, R3, R4) = (32, 24, 16, 63)`.

A word is a `UInt64`, so `+` is the addition modulo `2^64` of §3.1.

The RFC's `^` is exclusive-or (§2.3), which Lean writes `^^^`. -/

/-- The initialization vector, RFC 7693 §2.6.

Word `i` is `floor(2^64 * frac(sqrt(p)))`, where `p` is the `(i + 1)`-th prime.

These are also the initial hash values of SHA-512.

The kernel checks every word against its square root in the proofs. -/
def IV : Vector UInt64 8 := #v[
  0x6A09E667F3BCC908, 0xBB67AE8584CAA73B, 0x3C6EF372FE94F82B, 0xA54FF53A5F1D36F1,
  0x510E527FADE682D1, 0x9B05688C2B3E6C1F, 0x1F83D9ABFB41BD6B, 0x5BE0CD19137E2179]

/-- The message schedule, RFC 7693 §2.7.

Round `i` reads the 16 message words in the order of row `i mod 10`.

So rounds 10 and 11 of BLAKE2b reuse rows 0 and 1.

The kernel checks that each row is a permutation in the proofs. -/
def SIGMA : Vector (Vector (Fin 16) 16) 10 := #v[
  #v[ 0,  1,  2,  3,  4,  5,  6,  7,  8,  9, 10, 11, 12, 13, 14, 15],
  #v[14, 10,  4,  8,  9, 15, 13,  6,  1, 12,  0,  2, 11,  7,  5,  3],
  #v[11,  8, 12,  0,  5,  2, 15, 13, 10, 14,  3,  6,  7,  1,  9,  4],
  #v[ 7,  9,  3,  1, 13, 12, 11, 14,  2,  6,  5, 10,  4,  0, 15,  8],
  #v[ 9,  0,  5,  7,  2,  4, 10, 15, 14,  1, 11, 12,  6,  8,  3, 13],
  #v[ 2, 12,  6, 10,  0, 11,  8,  3,  4, 13,  7,  5, 15, 14,  1,  9],
  #v[12,  5,  1, 15, 14, 13,  4, 10,  0,  7,  6,  3,  9,  2,  8, 11],
  #v[13, 11,  7, 14, 12,  1,  3,  9,  5,  0, 15,  4,  8,  6,  2, 10],
  #v[ 6, 15, 14,  9, 11,  3,  0,  8, 12,  2, 13,  7,  1,  4, 10,  5],
  #v[10,  2,  8,  4,  7,  6,  1,  5, 15, 11,  9, 14,  3, 12, 13,  0]]

/-! ## The mixing function G -/

/-- Rotation of a word right by `n` bits, for `0 < n < 64`, RFC 7693 §2.3.

The RFC defines it as `(x >> n) ^ (x << (w - n))`.

Lean's `>>>` is the RFC's shift `>>`, so the rotation is spelled out. -/
@[inline] def rotr (x : UInt64) (n : UInt64) : UInt64 :=
  (x >>> n) ^^^ (x <<< (64 - n))

/-- The mixing function G, RFC 7693 §3.1.

It mixes the two message words `x` and `y` into the words `a`, `b`, `c` and `d` of the work vector. -/
def mix (v : Vector UInt64 16) (a b c d : Fin 16) (x y : UInt64) : Vector UInt64 16 :=
  let v := v.set a (v[a] + v[b] + x)
  let v := v.set d (rotr (v[d] ^^^ v[a]) 32)
  let v := v.set c (v[c] + v[d])
  let v := v.set b (rotr (v[b] ^^^ v[c]) 24)
  let v := v.set a (v[a] + v[b] + y)
  let v := v.set d (rotr (v[d] ^^^ v[a]) 16)
  let v := v.set c (v[c] + v[d])
  v.set b (rotr (v[b] ^^^ v[c]) 63)

/-! ## The compression function F -/

/-- Round `i` of F, RFC 7693 §3.2.

Read the work vector as a 4 x 4 matrix, row by row.

The round applies G to the four columns, then to the four diagonals.

The message words enter in the order of row `i mod 10` of the schedule. -/
def round (m : Vector UInt64 16) (i : Nat) (v : Vector UInt64 16) : Vector UInt64 16 :=
  let s := SIGMA[i % 10]
  -- The four columns, such as `v[0], v[4], v[8], v[12]`.
  let v := mix v 0 4  8 12 m[s[0]]  m[s[1]]
  let v := mix v 1 5  9 13 m[s[2]]  m[s[3]]
  let v := mix v 2 6 10 14 m[s[4]]  m[s[5]]
  let v := mix v 3 7 11 15 m[s[6]]  m[s[7]]
  -- The four diagonals, such as `v[0], v[5], v[10], v[15]`.
  let v := mix v 0 5 10 15 m[s[8]]  m[s[9]]
  let v := mix v 1 6 11 12 m[s[10]] m[s[11]]
  let v := mix v 2 7  8 13 m[s[12]] m[s[13]]
  mix v 3 4  9 14 m[s[14]] m[s[15]]

/-- The rounds `start` to `start + count - 1` of F, in order.

It recurses on the count, so the kernel can unfold it.

It is a tail call, so it compiles to a loop, even for `2^32 - 1` rounds. -/
def roundsFrom (m : Vector UInt64 16) (start : Nat) : Nat → Vector UInt64 16 → Vector UInt64 16
  | 0, v => v
  | count + 1, v => roundsFrom m (start + 1) count (round m start v)

/-- The compression function F, RFC 7693 §3.2, with `rounds` rounds.

- `h` is the state, 8 words.
- `m` is the message block, 16 words.
- `t0` and `t1` are the low and high words of the 128-bit offset counter `t`.
- `f` is the final block flag.

It returns the new state.

With 12 rounds it is the F of BLAKE2b. -/
def compress (rounds : Nat) (h : Vector UInt64 8) (m : Vector UInt64 16) (t0 t1 : UInt64)
    (f : Bool) : Vector UInt64 8 :=
  -- The work vector: the state, then the IV.
  let v : Vector UInt64 16 := h ++ IV
  -- Mix in the offset: `t mod 2^64` into word 12, `t >> 64` into word 13.
  let v := v.set 12 (v[12] ^^^ t0)
  let v := v.set 13 (v[13] ^^^ t1)
  -- The last block inverts all bits of word 14.
  let v := if f then v.set 14 (v[14] ^^^ 0xFFFFFFFFFFFFFFFF) else v
  -- Rounds `0` to `rounds - 1`.
  let v := roundsFrom m 0 rounds v
  -- XOR the two halves of the work vector into the state.
  Vector.ofFn fun i => h[i] ^^^ v[i] ^^^ v[i.val + 8]

end EthLib.Cryptography.Hash.Blake2b
