import Clean.Utils.Bitwise
import Clean.Utils.Vector

namespace Specs.SHA256

-- Round constants: first 32 bits of the fractional parts of cube roots of first 64 primes
def K : Vector UInt32 64 := #v[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5,
  0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3,
  0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc,
  0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
  0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13,
  0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3,
  0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5,
  0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208,
  0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2
]

-- Initial hash values: first 32 bits of fractional parts of square roots of first 8 primes
def H0 : Vector ℕ 8 := #v[
  0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
  0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19
]

def not32 (a : ℕ) : ℕ := a ^^^ 0xffffffff

-- σ₀(x) = ROTR7(x) XOR ROTR18(x) XOR SHR3(x)
def lowerSigma0 (x : ℕ) : ℕ := rotRight32 x 7 ^^^ rotRight32 x 18 ^^^ (x / 2^3)

-- σ₁(x) = ROTR17(x) XOR ROTR19(x) XOR SHR10(x)
def lowerSigma1 (x : ℕ) : ℕ := rotRight32 x 17 ^^^ rotRight32 x 19 ^^^ (x / 2^10)

-- Σ₀(x) = ROTR2(x) XOR ROTR13(x) XOR ROTR22(x)
def upperSigma0 (x : ℕ) : ℕ := rotRight32 x 2 ^^^ rotRight32 x 13 ^^^ rotRight32 x 22

-- Σ₁(x) = ROTR6(x) XOR ROTR11(x) XOR ROTR25(x)
def upperSigma1 (x : ℕ) : ℕ := rotRight32 x 6 ^^^ rotRight32 x 11 ^^^ rotRight32 x 25

def Ch (e f g : ℕ) : ℕ := (e &&& f) ^^^ (not32 e &&& g)

def Maj (a b c : ℕ) : ℕ := (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)

-- One round of the SHA-256 compression function
-- state = [a, b, c, d, e, f, g, h]
def sha256Round (state : Vector ℕ 8) (k w : ℕ) : Vector ℕ 8 :=
  let a := state[0]; let b := state[1]; let c := state[2]; let d := state[3]
  let e := state[4]; let f := state[5]; let g := state[6]; let h := state[7]
  let t1 := add32 (add32 (add32 (add32 h (upperSigma1 e)) (Ch e f g)) k) w
  let t2 := add32 (upperSigma0 a) (Maj a b c)
  #v[add32 t1 t2, a, b, c, add32 d t1, e, f, g]

-- Expand a 16-word block into a 64-word message schedule
def messageSchedule (block : Vector ℕ 16) : Vector ℕ 64 :=
  let init : Vector ℕ 64 := Vector.mapFinRange 64 fun i =>
    if h : i.val < 16 then block.get ⟨i.val, h⟩ else 0
  Fin.foldl 48 (fun w (i : Fin 48) =>
    let j := i.val + 16
    have hj   : j     < 64 := by omega
    have hj2  : j - 2  < 64 := by omega
    have hj7  : j - 7  < 64 := by omega
    have hj15 : j - 15 < 64 := by omega
    have hj16 : j - 16 < 64 := by omega
    let wj := add32 (add32 (lowerSigma1 (w.get ⟨j - 2,  hj2 ⟩))  (w.get ⟨j - 7,  hj7 ⟩))
                    (add32 (lowerSigma0 (w.get ⟨j - 15, hj15⟩)) (w.get ⟨j - 16, hj16⟩))
    w.set (⟨j, hj⟩ : Fin 64) wj) init

-- Apply 64 rounds of SHA-256 to the state using the message schedule
def sha256Compress (state : Vector ℕ 8) (w : Vector ℕ 64) : Vector ℕ 8 :=
  Fin.foldl 64 (fun s i => sha256Round s K[i].toNat w[i]) state

-- Process one 512-bit block (16 big-endian 32-bit words)
def compressBlock (state : Vector ℕ 8) (block : Vector ℕ 16) : Vector ℕ 8 :=
  let w := messageSchedule block
  let state' := sha256Compress state w
  Vector.mapFinRange 8 fun i => add32 state[i] state'[i]

-- Parse 4 bytes in big-endian order into a 32-bit word
def bytesToWord32BE (b0 b1 b2 b3 : ℕ) : ℕ :=
  b0 * 2^24 + b1 * 2^16 + b2 * 2^8 + b3

-- Parse 64 bytes into a block of 16 big-endian 32-bit words
def bytesToBlock (bytes : Vector ℕ 64) : Vector ℕ 16 :=
  Vector.mapFinRange 16 fun (i : Fin 16) =>
    have h0 : 4 * i.val     < 64 := by omega
    have h1 : 4 * i.val + 1 < 64 := by omega
    have h2 : 4 * i.val + 2 < 64 := by omega
    have h3 : 4 * i.val + 3 < 64 := by omega
    bytesToWord32BE (bytes.get ⟨4 * i.val,     h0⟩) (bytes.get ⟨4 * i.val + 1, h1⟩)
                    (bytes.get ⟨4 * i.val + 2, h2⟩) (bytes.get ⟨4 * i.val + 3, h3⟩)

-- SHA-256 padding (FIPS 180-4):
--   append 0x80, then zeros until message length ≡ 56 (mod 64) bytes,
--   then the original bit length as a big-endian 64-bit integer
def pad (msg : List ℕ) : List (Vector ℕ 16) :=
  let msgLen := msg.length
  let bitLen := msgLen * 8
  let zeros  := (55 + 64 - msgLen % 64) % 64
  let padded := msg ++ [0x80] ++ List.replicate zeros 0 ++ [
    bitLen / 2^56 % 256, bitLen / 2^48 % 256,
    bitLen / 2^40 % 256, bitLen / 2^32 % 256,
    bitLen / 2^24 % 256, bitLen / 2^16 % 256,
    bitLen / 2^8  % 256, bitLen         % 256
  ]
  let numBlocks := padded.length / 64
  List.range numBlocks |>.map fun i =>
    bytesToBlock (Vector.mapFinRange 64 fun j => padded.getD (64 * i + j.val) 0)

def sha256 (msg : List ℕ) : Vector ℕ 8 :=
  (pad msg).foldl compressBlock H0

end Specs.SHA256

namespace Specs.SHA256.Tests

-- SHA-256("") = e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855
-- SHA-256("abc") = ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad

-- #eval sha256 []
-- expected: #v[0xe3b0c442, 0x98fc1c14, 0x9afbf4c8, 0x996fb924,
--              0x27ae41e4, 0x649b934c, 0xa495991b, 0x7852b855]

-- #eval sha256 [0x61, 0x62, 0x63]
-- expected: #v[0xba7816bf, 0x8f01cfea, 0x414140de, 0x5dae2223,
--              0xb00361a3, 0x96177a9c, 0xb410ff61, 0xf20015ad]

example : sha256 [] = #v[
  0xe3b0c442, 0x98fc1c14, 0x9afbf4c8, 0x996fb924,
  0x27ae41e4, 0x649b934c, 0xa495991b, 0x7852b855
] := by native_decide

example : sha256 [0x61, 0x62, 0x63] = #v[
  0xba7816bf, 0x8f01cfea, 0x414140de, 0x5dae2223,
  0xb00361a3, 0x96177a9c, 0xb410ff61, 0xf20015ad
] := by native_decide

-- SHA-256("a") = ca978112ca1bbdcafac231b39a23dc4da786eff8147c4e72b9807785afee48bb
example : sha256 [0x61] = #v[
  0xca978112, 0xca1bbdca, 0xfac231b3, 0x9a23dc4d,
  0xa786eff8, 0x147c4e72, 0xb9807785, 0xafee48bb
] := by native_decide

-- SHA-256("The quick brown fox jumps over the lazy dog") =
--   d7a8fbb307d7809469ca9abcb0082e4f8d5651e46d3cdb762d02d0bf37c9e592
example : sha256 [
  0x54, 0x68, 0x65, 0x20, 0x71, 0x75, 0x69, 0x63, 0x6b, 0x20, 0x62, 0x72,
  0x6f, 0x77, 0x6e, 0x20, 0x66, 0x6f, 0x78, 0x20, 0x6a, 0x75, 0x6d, 0x70,
  0x73, 0x20, 0x6f, 0x76, 0x65, 0x72, 0x20, 0x74, 0x68, 0x65, 0x20, 0x6c,
  0x61, 0x7a, 0x79, 0x20, 0x64, 0x6f, 0x67
] = #v[
  0xd7a8fbb3, 0x07d78094, 0x69ca9abc, 0xb0082e4f,
  0x8d5651e4, 0x6d3cdb76, 0x2d02d0bf, 0x37c9e592
] := by native_decide

-- A single trailing byte change must produce a completely different digest:
-- SHA-256("The quick brown fox jumps over the lazy dog.") =
--   ef537f25c895bfa782526529a9b63d97aa631564d5d789c2b765448c8635fb6c
example : sha256 [
  0x54, 0x68, 0x65, 0x20, 0x71, 0x75, 0x69, 0x63, 0x6b, 0x20, 0x62, 0x72,
  0x6f, 0x77, 0x6e, 0x20, 0x66, 0x6f, 0x78, 0x20, 0x6a, 0x75, 0x6d, 0x70,
  0x73, 0x20, 0x6f, 0x76, 0x65, 0x72, 0x20, 0x74, 0x68, 0x65, 0x20, 0x6c,
  0x61, 0x7a, 0x79, 0x20, 0x64, 0x6f, 0x67, 0x2e
] = #v[
  0xef537f25, 0xc895bfa7, 0x82526529, 0xa9b63d97,
  0xaa631564, 0xd5d789c2, 0xb765448c, 0x8635fb6c
] := by native_decide

-- NIST FIPS 180-4 two-block test: 56-byte message forces a second padding block.
-- SHA-256("abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq") =
--   248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1
example : sha256 [
  0x61, 0x62, 0x63, 0x64, 0x62, 0x63, 0x64, 0x65, 0x63, 0x64, 0x65, 0x66,
  0x64, 0x65, 0x66, 0x67, 0x65, 0x66, 0x67, 0x68, 0x66, 0x67, 0x68, 0x69,
  0x67, 0x68, 0x69, 0x6a, 0x68, 0x69, 0x6a, 0x6b, 0x69, 0x6a, 0x6b, 0x6c,
  0x6a, 0x6b, 0x6c, 0x6d, 0x6b, 0x6c, 0x6d, 0x6e, 0x6c, 0x6d, 0x6e, 0x6f,
  0x6d, 0x6e, 0x6f, 0x70, 0x6e, 0x6f, 0x70, 0x71
] = #v[
  0x248d6a61, 0xd20638b8, 0xe5c02693, 0x0c3e6039,
  0xa33ce459, 0x64ff2167, 0xf6ecedd4, 0x19db06c1
] := by native_decide

-- NIST FIPS 180-4 multi-block test: 112-byte message spans three padded blocks.
-- SHA-256("abcdefghbcdefghicdefghij...nopqrstu") =
--   cf5b16a778af8380036ce59e7b0492370b249b11e8f07a51afac45037afee9d1
example : sha256 [
  0x61, 0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x62, 0x63, 0x64, 0x65,
  0x66, 0x67, 0x68, 0x69, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69, 0x6a,
  0x64, 0x65, 0x66, 0x67, 0x68, 0x69, 0x6a, 0x6b, 0x65, 0x66, 0x67, 0x68,
  0x69, 0x6a, 0x6b, 0x6c, 0x66, 0x67, 0x68, 0x69, 0x6a, 0x6b, 0x6c, 0x6d,
  0x67, 0x68, 0x69, 0x6a, 0x6b, 0x6c, 0x6d, 0x6e, 0x68, 0x69, 0x6a, 0x6b,
  0x6c, 0x6d, 0x6e, 0x6f, 0x69, 0x6a, 0x6b, 0x6c, 0x6d, 0x6e, 0x6f, 0x70,
  0x6a, 0x6b, 0x6c, 0x6d, 0x6e, 0x6f, 0x70, 0x71, 0x6b, 0x6c, 0x6d, 0x6e,
  0x6f, 0x70, 0x71, 0x72, 0x6c, 0x6d, 0x6e, 0x6f, 0x70, 0x71, 0x72, 0x73,
  0x6d, 0x6e, 0x6f, 0x70, 0x71, 0x72, 0x73, 0x74, 0x6e, 0x6f, 0x70, 0x71,
  0x72, 0x73, 0x74, 0x75
] = #v[
  0xcf5b16a7, 0x78af8380, 0x036ce59e, 0x7b049237,
  0x0b249b11, 0xe8f07a51, 0xafac4503, 0x7afee9d1
] := by native_decide

-- Padding boundary: 55 bytes is the last input that still fits in one 512-bit block;
-- 56 bytes is the first input that requires a second block.
example : (pad []).length = 1 := by native_decide
example : (pad (List.replicate 55 0)).length = 1 := by native_decide
example : (pad (List.replicate 56 0)).length = 2 := by native_decide
example : (pad (List.replicate 64 0)).length = 2 := by native_decide
example : (pad (List.replicate 119 0)).length = 2 := by native_decide
example : (pad (List.replicate 120 0)).length = 3 := by native_decide

-- Helper function unit tests.

-- not32 flips all 32 bits.
example : not32 0 = 0xffffffff := by native_decide
example : not32 0xffffffff = 0 := by native_decide
example : not32 0xaaaaaaaa = 0x55555555 := by native_decide

-- Ch(e,f,g) selects f where e=1 and g where e=0.
example : Ch 0xffffffff 0x12345678 0xdeadbeef = 0x12345678 := by native_decide
example : Ch 0 0x12345678 0xdeadbeef = 0xdeadbeef := by native_decide
example : Ch 0xff00ff00 0xaaaaaaaa 0x55555555 = 0xaa55aa55 := by native_decide

-- Maj(a,b,c) is the bitwise majority function.
example : Maj 0 0 0 = 0 := by native_decide
example : Maj 0xffffffff 0xffffffff 0xffffffff = 0xffffffff := by native_decide
example : Maj 0xffffffff 0xffffffff 0 = 0xffffffff := by native_decide
example : Maj 0xffffffff 0 0 = 0 := by native_decide
example : Maj 0xff00ff00 0x00ffff00 0xffff0000 = 0xffffff00 := by native_decide

-- σ₀, σ₁, Σ₀, Σ₁ on zero are zero, and on a single low bit they expose the rotation amounts.
example : lowerSigma0 0 = 0 := by native_decide
example : lowerSigma1 0 = 0 := by native_decide
example : upperSigma0 0 = 0 := by native_decide
example : upperSigma1 0 = 0 := by native_decide
-- lowerSigma0 1 = (1 <<< 25) ^ (1 <<< 14) ^ 0
example : lowerSigma0 1 = 0x02004000 := by native_decide
-- lowerSigma1 1 = (1 <<< 15) ^ (1 <<< 13) ^ 0
example : lowerSigma1 1 = 0x0000a000 := by native_decide
-- upperSigma0 1 = (1 <<< 30) ^ (1 <<< 19) ^ (1 <<< 10)
example : upperSigma0 1 = 0x40080400 := by native_decide
-- upperSigma1 1 = (1 <<< 26) ^ (1 <<< 21) ^ (1 <<< 7)
example : upperSigma1 1 = 0x04200080 := by native_decide
-- The rotations are all bijections of 32-bit words, so each Σ on 0xffffffff is 0xffffffff.
example : upperSigma0 0xffffffff = 0xffffffff := by native_decide
example : upperSigma1 0xffffffff = 0xffffffff := by native_decide
-- σ₀ and σ₁ include a SHR, so they drop the top 3 / 10 bits.
example : lowerSigma0 0xffffffff = 0x1fffffff := by native_decide
example : lowerSigma1 0xffffffff = 0x003fffff := by native_decide

-- bytesToWord32BE packs four bytes in big-endian order.
example : bytesToWord32BE 0x12 0x34 0x56 0x78 = 0x12345678 := by native_decide
example : bytesToWord32BE 0 0 0 0 = 0 := by native_decide
example : bytesToWord32BE 0xff 0xff 0xff 0xff = 0xffffffff := by native_decide
example : bytesToWord32BE 0xde 0xad 0xbe 0xef = 0xdeadbeef := by native_decide

-- The first padding block for the empty message is 0x80 followed by 63 zero bytes,
-- which packs into a schedule starting with 0x80000000 and ending with 0.
example : (pad [])[0]! = #v[
  0x80000000, 0, 0, 0, 0, 0, 0, 0,
  0,          0, 0, 0, 0, 0, 0, 0
] := by native_decide

end Specs.SHA256.Tests
