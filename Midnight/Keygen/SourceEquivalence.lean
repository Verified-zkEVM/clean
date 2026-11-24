import Midnight.Chips.KeyChecks
import Midnight.Keygen.Pipeline

/-! The key of an admitted circuit, derived from Rust's `usize` lowering of its layout. -/

namespace Midnight.Keygen
open Halo2 Chips

/-- The key of this exact admitted circuit. It is derived from Rust's `usize` lowering
(`Usize.layout`) once `KeyChecks.keyed` shows that lowering is the certificate's, with agreeing
fixed writes and placed constants; Rust checks neither of the last two. -/
def deriveFromCertificate {source : CS} {ops : Operations F} {k : Nat}
    {planner : Layout.Planner} (architecture : Architecture)
    (_ : CertifiedCircuit.Certificate source ops k planner)
    (monomialSrs : Array G1.Point) : Except String DerivedVK :=
  match Usize.check source ops k planner with
  | .error e => .error e
  | .ok () =>
    if KeyChecks.keyed source ops k planner then
      let l := Usize.layout source ops k planner
      deriveVK architecture k planner ops source l.fixed l.copies monomialSrs
    else .error "the key's layout is not the certificate's, fixed writes conflict or a constant \
      is unplaced"

theorem keyed_of_deriveFromCertificate {source : CS} {ops : Operations F} {k : Nat}
    {planner : Layout.Planner} {architecture : Architecture}
    {cert : CertifiedCircuit.Certificate source ops k planner} {monomialSrs : Array G1.Point}
    {key : DerivedVK} (h : deriveFromCertificate architecture cert monomialSrs = .ok key) :
    Usize.check source ops k planner = .ok () ∧ KeyChecks.keyed source ops k planner = true := by
  unfold deriveFromCertificate at h
  split at h
  · cases h
  · next hc =>
    split at h
    · next hk => exact ⟨hc, hk⟩
    · cases h

end Midnight.Keygen
