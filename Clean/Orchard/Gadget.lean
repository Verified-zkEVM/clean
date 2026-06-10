import Clean.Circuit
import Clean.Orchard.Ecc
import Clean.Orchard.Poseidon
import Clean.Utils.Tactics
import Clean.Utils.Tactics.ProvableStructDeriving

/-!
# Orchard gadget composition assertions

Clean approximations of source-level Orchard circuit gadget wiring.

References:
`orchard@0.14.0/src/circuit/gadget.rs`
- `value_commit_orchard`
- `derive_nullifier`

`orchard@0.14.0/src/circuit.rs`
- `Spend authority`

These assertions model how the Rust circuit connects outputs from fixed-base
multiplication, Poseidon, the field-addition chip, and complete point addition. They do
not model those sub-gadgets internally; their outputs and complete-addition auxiliary
witnesses are explicit row values.
-/

namespace Orchard
namespace Gadget

variable {F : Type} [Field F]

namespace ValueCommitment

variable {R : Type} [Zero R] [One R] [Add R] [Sub R] [Mul R] [OfNat R 2] [OfNat R 3]

structure Row (F : Type) where
  valueProductX : F
  valueProductY : F
  blindProductX : F
  blindProductY : F
  cvX : F
  cvY : F
  lambda : F
  alpha : F
  beta : F
  gamma : F
  delta : F
deriving ProvableStruct

def addRow (row : Row R) : Ecc.CompleteAddRow R where
  p := { x := row.valueProductX, y := row.valueProductY }
  q := { x := row.blindProductX, y := row.blindProductY }
  r := { x := row.cvX, y := row.cvY }
  lambda := row.lambda
  alpha := row.alpha
  beta := row.beta
  gamma := row.gamma
  delta := row.delta

def Spec (row : Row R) : Prop :=
  Ecc.CompleteAdd.Spec (addRow row)

def main (row : Var Row F) : Circuit F Unit := do
  Ecc.CompleteAdd.circuit (addRow row)

def circuit : FormalAssertion F Row where
  main
  Spec := Spec
  soundness := by
    circuit_proof_start [main, Spec, addRow, Ecc.CompleteAdd.circuit, Ecc.CompleteAdd.Spec]
    simp_all
  completeness := by
    circuit_proof_start [main, Spec, addRow, Ecc.CompleteAdd.circuit, Ecc.CompleteAdd.Spec]
    simp_all

namespace Entry

structure Row (F : Type) where
  valueProductX : F
  valueProductY : F
  blindProductX : F
  blindProductY : F
  cvX : F
  cvY : F
deriving ProvableStruct

def addInput {K : Type} (row : Row K) : Ecc.AddInputs K where
  p := { x := row.valueProductX, y := row.valueProductY }
  q := { x := row.blindProductX, y := row.blindProductY }

def output {K : Type} (row : Row K) : Ecc.Point K where
  x := row.cvX
  y := row.cvY

def Spec (row : Row Ecc.PallasBaseField) : Prop :=
  Ecc.pointCoords (output row) =
    CompElliptic.CurveForms.ShortWeierstrass.add
      (0 : Ecc.PallasBaseField)
      (Ecc.pointCoords (addInput row).p)
      (Ecc.pointCoords (addInput row).q)

def Assumptions (row : Row Ecc.PallasBaseField) : Prop :=
  Ecc.CompleteAdd.Entry.Assumptions (addInput row)

def main (row : Var Row Ecc.PallasBaseField) : Circuit Ecc.PallasBaseField Unit := do
  let cv ← Ecc.CompleteAdd.Entry.circuit (addInput row)
  assertZero (cv.x - row.cvX)
  assertZero (cv.y - row.cvY)

def circuit : FormalAssertion Ecc.PallasBaseField Row where
  main
  Assumptions := Assumptions
  Spec := Spec
  soundness := by
    circuit_proof_start [main, Spec, addInput, output, Ecc.CompleteAdd.Entry.circuit,
      Ecc.CompleteAdd.Entry.Spec]
    rcases h_holds with ⟨hAdd, hX, hY⟩
    have hx : env.get i₀ = input_cvX := by linear_combination hX
    have hy : env.get (i₀ + 1) = input_cvY := by linear_combination hY
    have hAdd' := hAdd h_assumptions
    rw [← hAdd']
    simp [Ecc.pointCoords, hx, hy]
  completeness := by
    circuit_proof_start [main, Spec, addInput, output, Ecc.CompleteAdd.Entry.circuit,
      Ecc.CompleteAdd.Entry.Spec, Assumptions, Ecc.CompleteAdd.Entry.Assumptions]
    constructor
    · exact h_assumptions
    · have hAdd := h_env h_assumptions
      have hPoint : Ecc.pointCoords { x := env.get i₀, y := env.get (i₀ + 1) } =
          Ecc.pointCoords { x := input_cvX, y := input_cvY } := hAdd.trans h_spec.symm
      constructor
      · have hx := congrArg Prod.fst hPoint
        simpa [Ecc.pointCoords, sub_eq_add_neg] using sub_eq_zero.mpr hx
      · have hy := congrArg Prod.snd hPoint
        simpa [Ecc.pointCoords, sub_eq_add_neg] using sub_eq_zero.mpr hy

end Entry

end ValueCommitment

namespace Nullifier

variable {R : Type} [Zero R] [One R] [Add R] [Sub R] [Mul R] [OfNat R 2] [OfNat R 3]

structure Row (F : Type) where
  poseidonHash : F
  psi : F
  scalar : F
  cmX : F
  cmY : F
  productX : F
  productY : F
  nfPointX : F
  nfPointY : F
  nf : F
  lambda : F
  alpha : F
  beta : F
  gamma : F
  delta : F
deriving ProvableStruct

def addRow (row : Row R) : Ecc.CompleteAddRow R where
  p := { x := row.cmX, y := row.cmY }
  q := { x := row.productX, y := row.productY }
  r := { x := row.nfPointX, y := row.nfPointY }
  lambda := row.lambda
  alpha := row.alpha
  beta := row.beta
  gamma := row.gamma
  delta := row.delta

def scalarCheck (row : Row R) : R :=
  row.poseidonHash + row.psi - row.scalar

def extractCheck (row : Row R) : R :=
  row.nfPointX - row.nf

def Spec (row : Row R) : Prop :=
  scalarCheck row = 0 ∧
    Ecc.CompleteAdd.Spec (addRow row) ∧
    extractCheck row = 0

def main (row : Var Row F) : Circuit F Unit := do
  assertZero (scalarCheck row)
  Ecc.CompleteAdd.circuit (addRow row)
  assertZero (extractCheck row)

def circuit : FormalAssertion F Row where
  main
  Spec := Spec
  soundness := by
    circuit_proof_start [main, Spec, scalarCheck, extractCheck, addRow,
      Ecc.CompleteAdd.circuit, Ecc.CompleteAdd.Spec]
    simp_all [sub_eq_add_neg]
  completeness := by
    circuit_proof_start [main, Spec, scalarCheck, extractCheck, addRow,
      Ecc.CompleteAdd.circuit, Ecc.CompleteAdd.Spec]
    simp_all [sub_eq_add_neg]

namespace Entry

structure Row (F : Type) where
  poseidonHash : F
  psi : F
  scalar : F
  cmX : F
  cmY : F
  productX : F
  productY : F
  nfPointX : F
  nfPointY : F
  nf : F
deriving ProvableStruct

def addInput {K : Type} (row : Row K) : Ecc.AddInputs K where
  p := { x := row.cmX, y := row.cmY }
  q := { x := row.productX, y := row.productY }

def output {K : Type} (row : Row K) : Ecc.Point K where
  x := row.nfPointX
  y := row.nfPointY

def Spec (row : Row Ecc.PallasBaseField) : Prop :=
  row.scalar = row.poseidonHash + row.psi ∧
    Ecc.pointCoords (output row) =
      CompElliptic.CurveForms.ShortWeierstrass.add
        (0 : Ecc.PallasBaseField)
        (Ecc.pointCoords (addInput row).p)
        (Ecc.pointCoords (addInput row).q) ∧
    row.nf = row.nfPointX

def Assumptions (row : Row Ecc.PallasBaseField) : Prop :=
  Ecc.CompleteAdd.Entry.Assumptions (addInput row)

def main (row : Var Row Ecc.PallasBaseField) : Circuit Ecc.PallasBaseField Unit := do
  assertZero (row.poseidonHash + row.psi - row.scalar)
  let nfPoint ← Ecc.CompleteAdd.Entry.circuit (addInput row)
  assertZero (nfPoint.x - row.nfPointX)
  assertZero (nfPoint.y - row.nfPointY)
  assertZero (row.nfPointX - row.nf)

def circuit : FormalAssertion Ecc.PallasBaseField Row where
  main
  Assumptions := Assumptions
  Spec := Spec
  soundness := by
    circuit_proof_start [main, Spec, addInput, output, Assumptions,
      Ecc.CompleteAdd.Entry.circuit, Ecc.CompleteAdd.Entry.Spec]
    rcases h_holds with ⟨hScalar, hAdd, hX, hY, hExtract⟩
    refine ⟨?_, ?_, ?_⟩
    · linear_combination -hScalar
    · have hx : env.get i₀ = input_nfPointX := by linear_combination hX
      have hy : env.get (i₀ + 1) = input_nfPointY := by linear_combination hY
      have hAdd' := hAdd h_assumptions
      rw [← hAdd']
      simp [Ecc.pointCoords, hx, hy]
    · linear_combination -hExtract
  completeness := by
    circuit_proof_start [main, Spec, addInput, output, Assumptions,
      Ecc.CompleteAdd.Entry.circuit, Ecc.CompleteAdd.Entry.Spec,
      Ecc.CompleteAdd.Entry.Assumptions]
    rcases h_spec with ⟨hScalar, hAddSpec, hExtract⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · linear_combination -hScalar
    · exact h_assumptions
    · have hAdd := h_env h_assumptions
      have hPoint : Ecc.pointCoords { x := env.get i₀, y := env.get (i₀ + 1) } =
          Ecc.pointCoords { x := input_nfPointX, y := input_nfPointY } := hAdd.trans hAddSpec.symm
      have hx := congrArg Prod.fst hPoint
      simpa [Ecc.pointCoords, sub_eq_add_neg] using sub_eq_zero.mpr hx
    · have hAdd := h_env h_assumptions
      have hPoint : Ecc.pointCoords { x := env.get i₀, y := env.get (i₀ + 1) } =
          Ecc.pointCoords { x := input_nfPointX, y := input_nfPointY } := hAdd.trans hAddSpec.symm
      have hy := congrArg Prod.snd hPoint
      simpa [Ecc.pointCoords, sub_eq_add_neg] using sub_eq_zero.mpr hy
    · linear_combination -hExtract

end Entry

end Nullifier

/-!
Nullifier wiring including the two-input Poseidon hash.

Reference:
`orchard@0.14.0/src/circuit/gadget.rs`
- `derive_nullifier`

This strengthens `Nullifier.circuit` with the source edge
`hash = PoseidonHash(nk, rho)`. The Poseidon permutation result is still explicit in
`Poseidon.Hash2.Row`; the Pow5 gate assertions in `Clean.Orchard.Poseidon` model the
round arithmetic separately.
-/
namespace NullifierWithHash

variable {R : Type} [Zero R] [One R] [Add R] [Sub R] [Mul R] [OfNat R 2] [OfNat R 3]

structure Row (F : Type) where
  hash : Poseidon.Hash2.Row F
  nullifier : Nullifier.Row F
deriving ProvableStruct

def hashOutputCheck (row : Row R) : R :=
  row.hash.hash - row.nullifier.poseidonHash

def Spec (row : Row R) : Prop :=
  Poseidon.Hash2.Spec row.hash ∧
    Nullifier.Spec row.nullifier ∧
    hashOutputCheck row = 0

def main (row : Var Row F) : Circuit F Unit := do
  Poseidon.Hash2.circuit row.hash
  Nullifier.circuit row.nullifier
  assertZero (hashOutputCheck row)

def circuit : FormalAssertion F Row where
  main
  Spec := Spec
  soundness := by
    circuit_proof_start [main, Spec, hashOutputCheck, Poseidon.Hash2.circuit,
      Poseidon.Hash2.Spec, Nullifier.circuit, Nullifier.Spec]
    rcases h_holds with ⟨hHash, hNullifier, hOutput⟩
    rcases hHash with ⟨hPad, hInitial0, hInitial1, hCapacity, hInput0, hInput1, hHash⟩
    rcases hPad with ⟨hPad0, hPad1, hPad2⟩
    simp_all [Poseidon.PadAndAdd.Spec, sub_eq_add_neg]
  completeness := by
    circuit_proof_start [main, Spec, hashOutputCheck, Poseidon.Hash2.circuit,
      Poseidon.Hash2.Spec, Nullifier.circuit, Nullifier.Spec]
    rcases h_spec with ⟨hHash, hNullifier, hOutput⟩
    rcases hHash with ⟨hPad, hInitial0, hInitial1, hCapacity, hInput0, hInput1, hHash⟩
    rcases hPad with ⟨hPad0, hPad1, hPad2⟩
    simp_all [Poseidon.PadAndAdd.Spec, sub_eq_add_neg]

namespace Entry

structure Row (F : Type) where
  hash : Poseidon.Hash2.Row F
  nullifier : Nullifier.Entry.Row F
deriving ProvableStruct

def hashOutputCheck {K : Type} [Sub K] (row : Row K) : K :=
  row.hash.hash - row.nullifier.poseidonHash

def Spec (row : Row Ecc.PallasBaseField) : Prop :=
  Poseidon.Hash2.Spec row.hash ∧
    Nullifier.Entry.Spec row.nullifier ∧
    row.hash.hash = row.nullifier.poseidonHash

def Assumptions (row : Row Ecc.PallasBaseField) : Prop :=
  Nullifier.Entry.Assumptions row.nullifier

def main (row : Var Row Ecc.PallasBaseField) : Circuit Ecc.PallasBaseField Unit := do
  Poseidon.Hash2.circuit row.hash
  Nullifier.Entry.circuit row.nullifier
  assertZero (hashOutputCheck row)

def circuit : FormalAssertion Ecc.PallasBaseField Row where
  main
  Assumptions := Assumptions
  Spec := Spec
  soundness := by
    circuit_proof_start [main, Spec, hashOutputCheck, Assumptions,
      Poseidon.Hash2.circuit, Poseidon.Hash2.Spec,
      Nullifier.Entry.circuit, Nullifier.Entry.Spec]
    rcases h_holds with ⟨hHash, hNullifier, hOutput⟩
    exact ⟨hHash, hNullifier h_assumptions,
      sub_eq_zero.mp (by simpa [sub_eq_add_neg] using hOutput)⟩
  completeness := by
    circuit_proof_start [main, Spec, hashOutputCheck, Assumptions,
      Poseidon.Hash2.circuit, Poseidon.Hash2.Spec,
      Nullifier.Entry.circuit, Nullifier.Entry.Spec, Nullifier.Entry.Assumptions]
    rcases h_spec with ⟨hHash, hNullifier, hOutput⟩
    exact ⟨hHash, ⟨h_assumptions, hNullifier⟩,
      by simpa [sub_eq_add_neg] using sub_eq_zero.mpr hOutput⟩

end Entry

end NullifierWithHash

/-!
Nullifier wiring including the Poseidon hash/permutation boundary.

Reference:
`orchard@0.14.0/src/circuit/gadget.rs`
- `derive_nullifier`

This strengthens `NullifierWithHash.circuit` by also connecting the two-input Poseidon
hash row to explicit permutation endpoint states, matching the `poseidon_sponge` boundary
used by `PoseidonHash::hash`.
-/
namespace NullifierWithPoseidonBoundary

variable {R : Type} [Zero R] [One R] [Add R] [Sub R] [Mul R] [OfNat R 2] [OfNat R 3]

structure Row (F : Type) where
  boundary : Poseidon.Hash2PermutationBoundary.Row F
  nullifier : Nullifier.Row F
deriving ProvableStruct

def hashOutputCheck (row : Row R) : R :=
  row.boundary.hash.hash - row.nullifier.poseidonHash

def Spec (row : Row R) : Prop :=
  Poseidon.Hash2PermutationBoundary.Spec row.boundary ∧
    Nullifier.Spec row.nullifier ∧
    hashOutputCheck row = 0

def main (row : Var Row F) : Circuit F Unit := do
  Poseidon.Hash2PermutationBoundary.circuit row.boundary
  Nullifier.circuit row.nullifier
  assertZero (hashOutputCheck row)

def circuit : FormalAssertion F Row where
  main
  Spec := Spec
  soundness := by
    circuit_proof_start [main, Spec, hashOutputCheck,
      Poseidon.Hash2PermutationBoundary.circuit, Poseidon.Hash2PermutationBoundary.Spec,
      Nullifier.circuit, Nullifier.Spec]
    rcases h_holds with ⟨hBoundary, hNullifier, hOutput⟩
    rcases hBoundary with ⟨hHash, hBoundary0, hBoundary1, hBoundary2, hBoundaryOutput⟩
    rcases hHash with ⟨hPad, hInitial0, hInitial1, hCapacity, hInput0, hInput1, hHash⟩
    rcases hPad with ⟨hPad0, hPad1, hPad2⟩
    simp_all [Poseidon.Hash2.Spec, Poseidon.PadAndAdd.Spec, sub_eq_add_neg]
  completeness := by
    circuit_proof_start [main, Spec, hashOutputCheck,
      Poseidon.Hash2PermutationBoundary.circuit, Poseidon.Hash2PermutationBoundary.Spec,
      Nullifier.circuit, Nullifier.Spec]
    rcases h_spec with ⟨hBoundary, hNullifier, hOutput⟩
    rcases hBoundary with ⟨hHash, hBoundary0, hBoundary1, hBoundary2, hBoundaryOutput⟩
    rcases hHash with ⟨hPad, hInitial0, hInitial1, hCapacity, hInput0, hInput1, hHash⟩
    rcases hPad with ⟨hPad0, hPad1, hPad2⟩
    simp_all [Poseidon.Hash2.Spec, Poseidon.PadAndAdd.Spec, sub_eq_add_neg]

namespace Entry

structure Row (F : Type) where
  boundary : Poseidon.Hash2PermutationBoundary.Row F
  nullifier : Nullifier.Entry.Row F
deriving ProvableStruct

def hashOutputCheck {K : Type} [Sub K] (row : Row K) : K :=
  row.boundary.hash.hash - row.nullifier.poseidonHash

def Spec (row : Row Ecc.PallasBaseField) : Prop :=
  Poseidon.Hash2PermutationBoundary.Spec row.boundary ∧
    Nullifier.Entry.Spec row.nullifier ∧
    row.boundary.hash.hash = row.nullifier.poseidonHash

def Assumptions (row : Row Ecc.PallasBaseField) : Prop :=
  Nullifier.Entry.Assumptions row.nullifier

def main (row : Var Row Ecc.PallasBaseField) : Circuit Ecc.PallasBaseField Unit := do
  Poseidon.Hash2PermutationBoundary.circuit row.boundary
  Nullifier.Entry.circuit row.nullifier
  assertZero (hashOutputCheck row)

def circuit : FormalAssertion Ecc.PallasBaseField Row where
  main
  Assumptions := Assumptions
  Spec := Spec
  soundness := by
    circuit_proof_start [main, Spec, hashOutputCheck, Assumptions,
      Poseidon.Hash2PermutationBoundary.circuit, Poseidon.Hash2PermutationBoundary.Spec,
      Nullifier.Entry.circuit, Nullifier.Entry.Spec]
    rcases h_holds with ⟨hBoundary, hNullifier, hOutput⟩
    exact ⟨hBoundary, hNullifier h_assumptions,
      sub_eq_zero.mp (by simpa [sub_eq_add_neg] using hOutput)⟩
  completeness := by
    circuit_proof_start [main, Spec, hashOutputCheck, Assumptions,
      Poseidon.Hash2PermutationBoundary.circuit, Poseidon.Hash2PermutationBoundary.Spec,
      Nullifier.Entry.circuit, Nullifier.Entry.Spec, Nullifier.Entry.Assumptions]
    rcases h_spec with ⟨hBoundary, hNullifier, hOutput⟩
    exact ⟨hBoundary, ⟨h_assumptions, hNullifier⟩,
      by simpa [sub_eq_add_neg] using sub_eq_zero.mpr hOutput⟩

end Entry

end NullifierWithPoseidonBoundary

/-!
Spend-authority wiring.

Reference:
`orchard@0.14.0/src/circuit.rs`
- `Spend authority`

The source computes `alpha_commitment = [alpha] SpendAuthG`, then
`rk = alpha_commitment + ak_P`, and constrains `rk` to public inputs. The fixed-base
product is explicit here; this assertion models the complete-addition wiring from that
product and `ak_P` to `rk`.
-/
namespace SpendAuth

variable {R : Type} [Zero R] [One R] [Add R] [Sub R] [Mul R] [OfNat R 2] [OfNat R 3]

structure Row (F : Type) where
  alphaProductX : F
  alphaProductY : F
  akX : F
  akY : F
  rkX : F
  rkY : F
  lambda : F
  alpha : F
  beta : F
  gamma : F
  delta : F
deriving ProvableStruct

def addRow (row : Row R) : Ecc.CompleteAddRow R where
  p := { x := row.alphaProductX, y := row.alphaProductY }
  q := { x := row.akX, y := row.akY }
  r := { x := row.rkX, y := row.rkY }
  lambda := row.lambda
  alpha := row.alpha
  beta := row.beta
  gamma := row.gamma
  delta := row.delta

def Spec (row : Row R) : Prop :=
  Ecc.CompleteAdd.Spec (addRow row)

def main (row : Var Row F) : Circuit F Unit := do
  Ecc.CompleteAdd.circuit (addRow row)

def circuit : FormalAssertion F Row where
  main
  Spec := Spec
  soundness := by
    circuit_proof_start [main, Spec, addRow, Ecc.CompleteAdd.circuit, Ecc.CompleteAdd.Spec]
    simp_all
  completeness := by
    circuit_proof_start [main, Spec, addRow, Ecc.CompleteAdd.circuit, Ecc.CompleteAdd.Spec]
    simp_all

namespace Entry

structure Row (F : Type) where
  alphaProductX : F
  alphaProductY : F
  akX : F
  akY : F
  rkX : F
  rkY : F
deriving ProvableStruct

def addInput {K : Type} (row : Row K) : Ecc.AddInputs K where
  p := { x := row.alphaProductX, y := row.alphaProductY }
  q := { x := row.akX, y := row.akY }

def output {K : Type} (row : Row K) : Ecc.Point K where
  x := row.rkX
  y := row.rkY

def Spec (row : Row Ecc.PallasBaseField) : Prop :=
  Ecc.pointCoords (output row) =
    CompElliptic.CurveForms.ShortWeierstrass.add
      (0 : Ecc.PallasBaseField)
      (Ecc.pointCoords (addInput row).p)
      (Ecc.pointCoords (addInput row).q)

def Assumptions (row : Row Ecc.PallasBaseField) : Prop :=
  Ecc.CompleteAdd.Entry.Assumptions (addInput row)

def main (row : Var Row Ecc.PallasBaseField) : Circuit Ecc.PallasBaseField Unit := do
  let rk ← Ecc.CompleteAdd.Entry.circuit (addInput row)
  assertZero (rk.x - row.rkX)
  assertZero (rk.y - row.rkY)

def circuit : FormalAssertion Ecc.PallasBaseField Row where
  main
  Assumptions := Assumptions
  Spec := Spec
  soundness := by
    circuit_proof_start [main, Spec, addInput, output, Assumptions,
      Ecc.CompleteAdd.Entry.circuit, Ecc.CompleteAdd.Entry.Spec]
    rcases h_holds with ⟨hAdd, hX, hY⟩
    have hx : env.get i₀ = input_rkX := by linear_combination hX
    have hy : env.get (i₀ + 1) = input_rkY := by linear_combination hY
    have hAdd' := hAdd h_assumptions
    rw [← hAdd']
    simp [Ecc.pointCoords, hx, hy]
  completeness := by
    circuit_proof_start [main, Spec, addInput, output, Assumptions,
      Ecc.CompleteAdd.Entry.circuit, Ecc.CompleteAdd.Entry.Spec,
      Ecc.CompleteAdd.Entry.Assumptions]
    constructor
    · exact h_assumptions
    · have hAdd := h_env h_assumptions
      have hPoint : Ecc.pointCoords { x := env.get i₀, y := env.get (i₀ + 1) } =
          Ecc.pointCoords { x := input_rkX, y := input_rkY } := hAdd.trans h_spec.symm
      constructor
      · have hx := congrArg Prod.fst hPoint
        simpa [Ecc.pointCoords, sub_eq_add_neg] using sub_eq_zero.mpr hx
      · have hy := congrArg Prod.snd hPoint
        simpa [Ecc.pointCoords, sub_eq_add_neg] using sub_eq_zero.mpr hy

end Entry

end SpendAuth

end Gadget
end Orchard
