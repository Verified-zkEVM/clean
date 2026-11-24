import Midnight.Field
import Clean.Specs.SHA256

/-!
Functional specification for the pinned Midnight SHA preimage circuit.

The reference is Clean's SHA-256 specification, including padding, message
expansion, all 64 rounds and feed-forward. The 24-byte specialization below is
only the public example's input length; it does not replace SHA by the gate
equations being verified. No circuit correctness is asserted in this module.
-/

namespace Midnight.SHA256.Spec

abbrev Message := Vector Nat 24
abbrev Digest := Vector Nat 32

def Bytes (message : Message) : Prop := ∀ i : Fin 24, message[i] < 256

/-- The exact padding used by the native 24-byte example: one block, 192 bits. -/
def paddedBytes (message : Message) : List Nat :=
  message.toList ++ [128] ++ List.replicate 31 0 ++ [0, 0, 0, 0, 0, 0, 0, 192]

def paddedBlockBytes (message : Message) : Vector Nat 64 :=
  Vector.mapFinRange 64 fun i => (paddedBytes message).getD i.val 0

def block (message : Message) : Vector Nat 16 :=
  Specs.SHA256.bytesToBlock (paddedBlockBytes message)

/-- The fixed-length padding is exactly the reference SHA padding. -/
theorem pad_eq_single_block (message : Message) :
    Specs.SHA256.pad message.toList = [block message] := by
  simp [Specs.SHA256.pad, block, paddedBlockBytes, paddedBytes]

def hashWords (message : Message) : Vector Nat 8 :=
  Specs.SHA256.sha256 message.toList

theorem hashWords_eq_compressBlock (message : Message) :
    hashWords message = Specs.SHA256.compressBlock Specs.SHA256.H0 (block message) := by
  simp [hashWords, Specs.SHA256.sha256, pad_eq_single_block]

/-- SHA exposes each 32-bit word most-significant byte first. -/
def wordByte (word : Nat) (index : Fin 4) : Nat :=
  word / 2 ^ (8 * (3 - index.val)) % 256

theorem wordByte_lt (word : Nat) (index : Fin 4) : wordByte word index < 256 :=
  Nat.mod_lt _ (by decide)

def encodeDigest (words : Vector Nat 8) : Digest :=
  Vector.mapFinRange 32 fun i => wordByte (words.get ⟨i.val / 4, by omega⟩) ⟨i.val % 4, by omega⟩

theorem encodeDigest_byte_lt (words : Vector Nat 8) (i : Fin 32) :
    (encodeDigest words)[i] < 256 := by
  rw [encodeDigest, Vector.getElemFin_mapFinRange]
  exact wordByte_lt _ _

def digest (message : Message) : Digest := encodeDigest (hashWords message)

theorem digest_byte_lt (message : Message) (i : Fin 32) : (digest message)[i] < 256 := by
  exact encodeDigest_byte_lt (hashWords message) i

end Midnight.SHA256.Spec
