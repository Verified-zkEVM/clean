import Midnight.Keygen.Domain
import CompPoly.Data.Bytes.LittleEndian
import EthLib.Cryptography.Hash.Blake2b

/-! BLAKE2b-512 with a personalization, as `VerifyingKey::from_parts` hashes the key: RFC 7693
§§2–3 and the pinned `blake2b_simd` crate's `Params::to_words`, over the vendored EthLib
compression function F at 12 rounds. -/

namespace Midnight.Keygen.Blake2b
open EthLib.Cryptography.Hash.Blake2b (IV)

private def wordLE (input : ByteArray) (offset : Nat) : UInt64 :=
  UInt64.ofNat (CompPoly.Bytes.ofListLE ((List.range 8).map fun i => input.get! (offset + i)))

/-- Sequential, unkeyed BLAKE2b with a 64-byte digest and ≤16 personalization bytes. -/
def hash (input : ByteArray) (personal : ByteArray := ByteArray.empty) : Except String ByteArray := do
  unless personal.size ≤ 16 do throw "BLAKE2b personalization exceeds 16 bytes"
  let h₀ := ((IV.set 0 (IV[0] ^^^ 0x01010040)).set 6 (IV[6] ^^^ wordLE personal 0)).set 7
    (IV[7] ^^^ wordLE personal 8)
  let blocks := max 1 ((input.size + 127) / 128)
  let h := (List.range blocks).foldl (fun h block =>
    let offset := block * 128
    let count := min input.size (offset + 128)
    EthLib.Cryptography.Hash.Blake2b.compress 12 h
      (Vector.ofFn fun i => wordLE input (offset + 8 * i.val))
      (UInt64.ofNat count) (UInt64.ofNat (count / 2 ^ 64)) (block + 1 == blocks)) h₀
  return ⟨h.toArray.flatMap fun word => (CompPoly.Bytes.toListLE 8 word.toNat).toArray⟩

def hex (bytes : ByteArray) : String :=
  String.join (bytes.data.toList.map fun b => b.toBitVec.toHex)

end Midnight.Keygen.Blake2b
