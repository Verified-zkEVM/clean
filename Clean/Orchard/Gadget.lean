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

end SpendAuth

end Gadget
end Orchard
