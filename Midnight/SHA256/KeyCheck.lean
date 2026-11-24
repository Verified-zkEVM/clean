import Midnight.SHA256.SrsLiteral
import Midnight.SHA256.Admission.Certificate
import Midnight.SHA256.SynthesisLayout
import Midnight.Keygen.Pipeline
import Midnight.Chips.CertifiedCircuit
import Midnight.SHA256.Configure
import Midnight.Keygen.SourceEquivalence
import Clean.Specs.SHA256

/-! Lean's executable key derivation against the digest Rust commits for the same key. Both
checks are `native_decide`: in the kernel they would take hours of FFTs and MSMs. Digests are
Clean's SHA-256 specification. -/
namespace Midnight.SHA256.KeyCheck
open Midnight.Keygen Specs.SHA256

/-- Lean's key derivation for the admitted circuit (`Admission.native_certificate`, the
operations `formal_instance_sha256` is about) on the public SRS. -/
def derivation : Except String DerivedVK := do
  let srs ← srsLiteral.mapM fun (x, y) => (G1.ofCoords? x y).elim (throw "SRS point off the curve") pure
  deriveFromCertificate architecture Admission.native_certificate srs

/-- `Specs.SHA256.pad`, reading the padded message from an array: `List.getD` makes the
specification quadratic, too slow for the SRS's 786432 bytes. -/
def padArray (msg : List Nat) : List (Vector Nat 16) :=
  let msgLen := msg.length
  let bitLen := msgLen * 8
  let zeros := (55 + 64 - msgLen % 64) % 64
  let padded := (msg ++ [0x80] ++ List.replicate zeros 0 ++ [
    bitLen / 2^56 % 256, bitLen / 2^48 % 256, bitLen / 2^40 % 256, bitLen / 2^32 % 256,
    bitLen / 2^24 % 256, bitLen / 2^16 % 256, bitLen / 2^8 % 256, bitLen % 256]).toArray
  List.range (padded.size / 64) |>.map fun i =>
    bytesToBlock (Vector.mapFinRange 64 fun j => padded.getD (64 * i + j.val) 0)

theorem padArray_eq (msg : List Nat) : padArray msg = pad msg := by
  simp only [padArray, pad, List.size_toArray, Array.getD_eq_getD_getElem?, List.getElem?_toArray,
    List.getD_eq_getElem?_getD]

/-- Clean's SHA-256 of a byte string, as 32 big-endian bytes. -/
def sha256Bytes (bytes : ByteArray) : ByteArray :=
  ⟨(sha256 (bytes.data.toList.map UInt8.toNat)).toArray.flatMap fun word =>
    (G1.bytesBE 4 word).toArray⟩

/-- midnight-zk's `zk_stdlib/tests/static_vks/ShaPreImageCircuitVk`: the SHA-256 of the
preimage example's key in `SerdeFormat::RawBytes`. -/
def shaPreImageCircuitVk : ByteArray := ⟨#[
  0x07, 0x1b, 0xd2, 0x9a, 0xef, 0x0b, 0xff, 0xdb, 0x7b, 0x69, 0x9b, 0x46, 0x7d, 0xf5, 0x4f, 0xcc,
  0x8e, 0x76, 0xac, 0x56, 0x44, 0xb3, 0x12, 0x45, 0x36, 0x8b, 0xb9, 0xe5, 0xfc, 0xf8, 0x91, 0x83]⟩

/-- The SRS literal as Rust's raw points: big-endian x, then y. -/
def srsBytes : ByteArray :=
  ⟨(srsLiteral.toList.flatMap fun (x, y) => G1.bytesBE 48 x ++ G1.bytesBE 48 y).toArray⟩

/-- SHA-256 of the 2^13 monomial points of `zk_stdlib/examples/assets/bls_filecoin_2p19`
(the bytes after its 4-byte header). -/
def filecoinPoints : ByteArray := ⟨#[
  0x71, 0x19, 0xc3, 0x61, 0xa1, 0xb9, 0xd9, 0x09, 0x02, 0x29, 0xe0, 0x8c, 0x7d, 0xa1, 0xcc, 0x7b,
  0x16, 0xdc, 0x88, 0xe5, 0x4f, 0x1e, 0xeb, 0x46, 0xe6, 0x87, 0x26, 0xbd, 0x6b, 0xcd, 0x73, 0x79]⟩

/-- Lean derives the key from the SRS literal, and its `RawBytes` encoding hashes to the
digest Rust commits. -/
theorem rust_key :
    (derivation.toOption.map fun key => sha256Bytes key.raw) = some shaPreImageCircuitVk := by
  native_decide

/-- The SRS literal, written as Rust's raw points, is the Filecoin setup's prefix. The
derivation rejects noncanonical points, so these bytes determine the literal. -/
theorem srs_anchor : sha256Bytes srsBytes = filecoinPoints := by
  rw [sha256Bytes, sha256, ← padArray_eq]
  native_decide

end Midnight.SHA256.KeyCheck
