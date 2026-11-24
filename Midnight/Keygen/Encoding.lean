import Midnight.Keygen.G1
import Midnight.Keygen.Domain
import Midnight.Keygen.Blake2b

/-! The key bytes `zk_stdlib::interface::MidnightVK::write` produces, and the input
`VerifyingKey::from_parts` hashes into the transcript representative. -/
namespace Midnight.Keygen

/-- `ZkStdLibArch` version 2 in its serialization order. -/
structure Architecture where
  jubjub : Bool := false
  poseidon : Bool := false
  sha2_256 : Bool := false
  sha2_512 : Bool := false
  keccak_256 : Bool := false
  sha3_256 : Bool := false
  blake2b : Bool := false
  secp256k1 : Bool := false
  p256 : Bool := false
  bls12_381 : Bool := false
  curve25519 : Bool := false
  base64 : Bool := false
  automaton : Bool := false
  nbArithCols : UInt8 := 5
  nrPow2rangeCols : UInt8 := 1
  deriving DecidableEq, Repr

def Architecture.bytes (a : Architecture) : List UInt8 :=
  CompPoly.Bytes.toListLE 4 2 ++
    [a.jubjub, a.poseidon, a.sha2_256, a.sha2_512, a.keccak_256, a.sha3_256, a.blake2b,
      a.secp256k1, a.p256, a.bls12_381, a.curve25519, a.base64, a.automaton].map
      (fun b => if b then 1 else 0) ++
    [a.nbArithCols, a.nrPow2rangeCols]

/-- `SerdeFormat::Processed` (compressed) or `RawBytes` (uncompressed) for one point. -/
def pointBytes (compressed : Bool) (point : G1.Point) : List UInt8 :=
  (if compressed then G1.encodeCompressed point else G1.encodeRaw point).data.toList

/-- The inner halo2 key, version 3. -/
def innerBytes (compressed : Bool) (k : UInt8) (commitments : Array G1.Point) : List UInt8 :=
  [3, k] ++ commitments.toList.flatMap (pointBytes compressed)

def encodeVK (architecture : Architecture) (k : UInt8) (publicInputs : Nat) (compressed : Bool)
    (commitments : Array G1.Point) : ByteArray :=
  ⟨(architecture.bytes ++ [k] ++ CompPoly.Bytes.toListLE 4 publicInputs ++
    innerBytes compressed k commitments).toArray⟩

/-- The raw inner key, then the `Debug` text of domain and constraint system. -/
def transcriptInput (innerRawKey : ByteArray) (k degree : Nat) (pinnedCS : String) : ByteArray :=
  innerRawKey ++ (domainDebug k degree).toUTF8 ++ pinnedCS.toUTF8

/-- BLAKE2b-512 with personalization `Halo2-Verify-Key`, reduced into the scalar field. -/
def transcriptRepresentative (input : ByteArray) : Except String Nat := do
  let digest ← Blake2b.hash input "Halo2-Verify-Key".toUTF8
  return CompPoly.Bytes.ofByteArrayLE digest % BLS12_381.scalarFieldSize

end Midnight.Keygen
