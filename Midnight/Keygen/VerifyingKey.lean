import Midnight.Keygen.Encoding

/-! A derived verification key: its commitments, both encodings and the transcript hash input. -/

namespace Midnight.Keygen

/-- The serialization of a derived key's bytes. -/
inductive VKFormat where
  /-- `MidnightVK::write`: architecture, `k`, public-input count, then the halo2 key. Only a
  stdlib configuration has one, since `MidnightVK::read` rebuilds the constraint system from
  the architecture. -/
  | midnight (architecture : Architecture) (publicInputs : UInt32)
  /-- halo2's `VerifyingKey::write`. -/
  | halo2
  deriving DecidableEq, Repr

structure DerivedVK where
  commitments : Array G1.Point
  raw : ByteArray
  processed : ByteArray
  transcript : ByteArray
  transcriptRepr : Nat
  format : VKFormat
  deriving DecidableEq

end Midnight.Keygen
