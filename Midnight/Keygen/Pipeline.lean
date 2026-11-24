import Midnight.Keygen.Configure
import Midnight.Keygen.Permutation
import Midnight.Keygen.Commit
import Midnight.Keygen.Encoding
import Midnight.Keygen.VerifyingKey
import Midnight.SHA256.Configure
import Midnight.Poseidon.Configure
import Midnight.Chips.Planner

/-! Key derivation from a configured constraint system, its fixed matrix and copies, all supplied
by the caller; no data captured from Rust is loaded here. The key is in MidnightVK format when the
system is a ported stdlib configuration under the Simple planner, else in halo2's. -/

namespace Midnight.Keygen
open Halo2

private def VKFormat.encode (format : VKFormat) (k : UInt8)
    (compressed : Bool) (commitments : Array G1.Point) : ByteArray :=
  match format with
  | .halo2 => ⟨(innerBytes compressed k commitments).toArray⟩
  | .midnight architecture publicInputs =>
    encodeVK architecture k publicInputs.toNat compressed commitments

/-- `ZkStdLib::configure(architecture, k - 1)` for the architectures ported to Lean. -/
def stdlibSource? (architecture : Architecture) : Option CS :=
  if architecture = SHA256.architecture then some SHA256.configured
  else if architecture = Poseidon.architecture then some Poseidon.configured else none

/-- `nb_public_inputs`: the native chip's `instance_offset`, which only `constrain_as_public_input`
advances, each by one layouter `constrain_instance` on instance column 1 (native_chip.rs:645-653). -/
def publicInputCount (ops : Operations F) : UInt32 :=
  .ofNat (ops.countP fun | .constrainInstance _ column _ => column.index == 1 | _ => false)

/-- `MidnightVK` when `configured` is the stdlib configuration of `architecture` (the same
pinned constraint system, so `MidnightVK::read` rebuilds this key) laid out by `setup_vk`'s
`MidnightCircuit`, whose planner is Simple (interface.rs:386); else halo2's key. -/
def keyFormat (architecture : Architecture) (planner : Chips.Layout.Planner) (ops : Operations F)
    (configured : CS) : VKFormat :=
  if decide (planner = .simple) &&
      (stdlibSource? architecture).any (·.pinnedDebug == configured.pinnedDebug) then
    .midnight architecture (publicInputCount ops)
  else .halo2

private def assembleVK (format : VKFormat) (k : Nat)
    (finalized : CS) (commitments : Array G1.Point) : Except String DerivedVK := do
  unless k ≤ 32 && finalized.degree % 2 ^ 32 != 0 && extendedK k finalized.degree ≤ 32 do
    throw "domain exceeds the scalar field's two-adicity"
  unless finalized.numSelectors == 0 do
    throw "selectors must be finalized before assembling a verification key"
  unless finalized.selectorFixedStart.isSome do
    throw "constraint system has not undergone selector finalization"
  unless finalized.trashcans.all (fun g => !g.selector.simple) do
    throw "additive arguments require complex selectors"
  unless 2 ^ k ≥ finalized.blindingFactors + 3 do
    throw "domain is smaller than the constraint system's minimum rows"
  unless commitments.size == finalized.numFixed + finalized.permutation.size do
    throw "incorrect number of commitments for the derived configuration"
  let raw := format.encode (UInt8.ofNat k) false commitments
  let processed := format.encode (UInt8.ofNat k) true commitments
  let transcript := transcriptInput ⟨(innerBytes false (UInt8.ofNat k) commitments).toArray⟩
    k finalized.degree finalized.pinnedDebug
  let transcriptRepr ← transcriptRepresentative transcript
  return ⟨commitments, raw, processed, transcript, transcriptRepr, format⟩

private def deriveWith (format : VKFormat) (k : Nat)
    (configured : CS) (fixed : Array (Array Nat))
    (copies : List (Nat × Nat × Nat × Nat))
    (monomialSrs : Array G1.Point) : Except String DerivedVK := do
  unless configured.selectorFixedStart.isNone do
    throw "deriveVK requires an unfinalized constraint system"
  unless configured.trashcans.all (fun g => !g.selector.simple) do
    throw "additive arguments require complex selectors"
  configured.validate
  -- `EvaluationDomain::new(degree as u32, k)`: a residue of 0 underflows `j - 1` (domain.rs:56).
  unless k ≤ 32 && configured.degree % 2 ^ 32 != 0 && extendedK k configured.degree ≤ 32 do
    throw "domain exceeds the scalar field's two-adicity"
  let n := 2 ^ k
  unless n ≥ configured.blindingFactors + 3 do
    throw "domain is smaller than the constraint system's minimum rows"
  let finalized := configured.finalize
  unless fixed.size == finalized.numFixed && fixed.all (·.size == n) do
    throw "fixed matrix dimensions differ from the configured domain"
  unless monomialSrs.size == n do
    throw "monomial setup length differs from the configured domain"
  unless fixed.all (·.all (· < BLS12_381.scalarFieldSize)) do
    throw "fixed values are not canonical scalars"
  let permutations ← derivePermutationPolynomials k configured.permutation.size copies
  let some D := if hk : k ≤ 32 then some (domain k hk) else none
    | throw "domain exceeds the scalar field's two-adicity"
  let columns := fixed.map (fun column => column.map fun v : Nat => (v : F)) ++ permutations
  -- One task per column: `parMap` is `List.map` (CompElliptic `parMap_eq_map`).
  let commitments ← (CompElliptic.Curves.Pasta.Fast.Msm.parMap (commit monomialSrs D)
    columns.toList).toArray.mapM id
  assembleVK format k finalized commitments

/-- Derive the verification key in `keyFormat`, which the key records. -/
def deriveVK (architecture : Architecture) (k : Nat) (planner : Chips.Layout.Planner)
    (ops : Operations F) (configured : CS) (fixed : Array (Array Nat))
    (copies : List (Nat × Nat × Nat × Nat))
    (monomialSrs : Array G1.Point) : Except String DerivedVK :=
  deriveWith (keyFormat architecture planner ops configured) k configured fixed copies monomialSrs

end Midnight.Keygen
