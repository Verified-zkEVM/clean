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

def constraints (row : Row R) : Prop :=
  Ecc.CompleteAdd.constraints (addRow row)

def main (row : Var Row F) : Circuit F Unit := do
  Ecc.CompleteAdd.main (addRow row)

def circuit : FormalAssertion F Row where
  main
  Spec := constraints
  soundness := by
    circuit_proof_start [main, constraints, addRow, Ecc.CompleteAdd.main,
      Ecc.CompleteAdd.constraints, Ecc.CompleteAdd.poly1, Ecc.CompleteAdd.poly2,
      Ecc.CompleteAdd.poly3a, Ecc.CompleteAdd.poly3b, Ecc.CompleteAdd.poly3c,
      Ecc.CompleteAdd.poly3d, Ecc.CompleteAdd.poly4a, Ecc.CompleteAdd.poly4b,
      Ecc.CompleteAdd.poly5a, Ecc.CompleteAdd.poly5b, Ecc.CompleteAdd.poly6a,
      Ecc.CompleteAdd.poly6b, Ecc.CompleteAdd.nonexceptionalXR,
      Ecc.CompleteAdd.nonexceptionalYR, Ecc.CompleteAdd.ifAlpha,
      Ecc.CompleteAdd.ifBeta, Ecc.CompleteAdd.ifGamma, Ecc.CompleteAdd.ifDelta,
      Ecc.CompleteAdd.xQMinusXP, Ecc.CompleteAdd.xPMinusXR,
      Ecc.CompleteAdd.yQPlusYP]
    simp_all [sub_eq_add_neg]
  completeness := by
    circuit_proof_start [main, constraints, addRow, Ecc.CompleteAdd.main,
      Ecc.CompleteAdd.constraints, Ecc.CompleteAdd.poly1, Ecc.CompleteAdd.poly2,
      Ecc.CompleteAdd.poly3a, Ecc.CompleteAdd.poly3b, Ecc.CompleteAdd.poly3c,
      Ecc.CompleteAdd.poly3d, Ecc.CompleteAdd.poly4a, Ecc.CompleteAdd.poly4b,
      Ecc.CompleteAdd.poly5a, Ecc.CompleteAdd.poly5b, Ecc.CompleteAdd.poly6a,
      Ecc.CompleteAdd.poly6b, Ecc.CompleteAdd.nonexceptionalXR,
      Ecc.CompleteAdd.nonexceptionalYR, Ecc.CompleteAdd.ifAlpha,
      Ecc.CompleteAdd.ifBeta, Ecc.CompleteAdd.ifGamma, Ecc.CompleteAdd.ifDelta,
      Ecc.CompleteAdd.xQMinusXP, Ecc.CompleteAdd.xPMinusXR,
      Ecc.CompleteAdd.yQPlusYP]
    simp_all [sub_eq_add_neg]

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

def constraints (row : Row R) : Prop :=
  scalarCheck row = 0 ∧
    Ecc.CompleteAdd.constraints (addRow row) ∧
    extractCheck row = 0

def main (row : Var Row F) : Circuit F Unit := do
  assertZero (scalarCheck row)
  Ecc.CompleteAdd.main (addRow row)
  assertZero (extractCheck row)

def circuit : FormalAssertion F Row where
  main
  Spec := constraints
  soundness := by
    circuit_proof_start [main, constraints, scalarCheck, extractCheck, addRow,
      Ecc.CompleteAdd.main, Ecc.CompleteAdd.constraints, Ecc.CompleteAdd.poly1,
      Ecc.CompleteAdd.poly2, Ecc.CompleteAdd.poly3a, Ecc.CompleteAdd.poly3b,
      Ecc.CompleteAdd.poly3c, Ecc.CompleteAdd.poly3d, Ecc.CompleteAdd.poly4a,
      Ecc.CompleteAdd.poly4b, Ecc.CompleteAdd.poly5a, Ecc.CompleteAdd.poly5b,
      Ecc.CompleteAdd.poly6a, Ecc.CompleteAdd.poly6b,
      Ecc.CompleteAdd.nonexceptionalXR, Ecc.CompleteAdd.nonexceptionalYR,
      Ecc.CompleteAdd.ifAlpha, Ecc.CompleteAdd.ifBeta, Ecc.CompleteAdd.ifGamma,
      Ecc.CompleteAdd.ifDelta, Ecc.CompleteAdd.xQMinusXP,
      Ecc.CompleteAdd.xPMinusXR, Ecc.CompleteAdd.yQPlusYP]
    simp_all [sub_eq_add_neg]
  completeness := by
    circuit_proof_start [main, constraints, scalarCheck, extractCheck, addRow,
      Ecc.CompleteAdd.main, Ecc.CompleteAdd.constraints, Ecc.CompleteAdd.poly1,
      Ecc.CompleteAdd.poly2, Ecc.CompleteAdd.poly3a, Ecc.CompleteAdd.poly3b,
      Ecc.CompleteAdd.poly3c, Ecc.CompleteAdd.poly3d, Ecc.CompleteAdd.poly4a,
      Ecc.CompleteAdd.poly4b, Ecc.CompleteAdd.poly5a, Ecc.CompleteAdd.poly5b,
      Ecc.CompleteAdd.poly6a, Ecc.CompleteAdd.poly6b,
      Ecc.CompleteAdd.nonexceptionalXR, Ecc.CompleteAdd.nonexceptionalYR,
      Ecc.CompleteAdd.ifAlpha, Ecc.CompleteAdd.ifBeta, Ecc.CompleteAdd.ifGamma,
      Ecc.CompleteAdd.ifDelta, Ecc.CompleteAdd.xQMinusXP,
      Ecc.CompleteAdd.xPMinusXR, Ecc.CompleteAdd.yQPlusYP]
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

def constraints (row : Row R) : Prop :=
  Poseidon.Hash2.constraints row.hash ∧
    Nullifier.constraints row.nullifier ∧
    hashOutputCheck row = 0

def main (row : Var Row F) : Circuit F Unit := do
  assertZero (Poseidon.PadAndAdd.output0Check row.hash.absorbed)
  assertZero (Poseidon.PadAndAdd.output1Check row.hash.absorbed)
  assertZero (Poseidon.PadAndAdd.capacityCheck row.hash.absorbed)
  assertZero (Poseidon.Hash2.initial0Check row.hash)
  assertZero (Poseidon.Hash2.initial1Check row.hash)
  assertZero (Poseidon.Hash2.capacityCheck row.hash)
  assertZero (Poseidon.Hash2.input0Check row.hash)
  assertZero (Poseidon.Hash2.input1Check row.hash)
  assertZero (Poseidon.Hash2.hashCheck row.hash)
  assertZero (Nullifier.scalarCheck row.nullifier)
  Ecc.CompleteAdd.main (Nullifier.addRow row.nullifier)
  assertZero (Nullifier.extractCheck row.nullifier)
  assertZero (hashOutputCheck row)

def circuit : FormalAssertion F Row where
  main
  Spec := constraints
  soundness := by
    circuit_proof_start [main, constraints, hashOutputCheck, Poseidon.Hash2.constraints,
      Poseidon.Hash2.initial0Check, Poseidon.Hash2.initial1Check,
      Poseidon.Hash2.capacityCheck, Poseidon.Hash2.input0Check,
      Poseidon.Hash2.input1Check, Poseidon.Hash2.hashCheck,
      Poseidon.PadAndAdd.output0Check, Poseidon.PadAndAdd.output1Check,
      Poseidon.PadAndAdd.capacityCheck, Nullifier.constraints, Nullifier.scalarCheck,
      Nullifier.extractCheck, Nullifier.addRow, Ecc.CompleteAdd.main,
      Ecc.CompleteAdd.constraints, Ecc.CompleteAdd.poly1, Ecc.CompleteAdd.poly2,
      Ecc.CompleteAdd.poly3a, Ecc.CompleteAdd.poly3b, Ecc.CompleteAdd.poly3c,
      Ecc.CompleteAdd.poly3d, Ecc.CompleteAdd.poly4a, Ecc.CompleteAdd.poly4b,
      Ecc.CompleteAdd.poly5a, Ecc.CompleteAdd.poly5b, Ecc.CompleteAdd.poly6a,
      Ecc.CompleteAdd.poly6b, Ecc.CompleteAdd.nonexceptionalXR,
      Ecc.CompleteAdd.nonexceptionalYR, Ecc.CompleteAdd.ifAlpha,
      Ecc.CompleteAdd.ifBeta, Ecc.CompleteAdd.ifGamma, Ecc.CompleteAdd.ifDelta,
      Ecc.CompleteAdd.xQMinusXP, Ecc.CompleteAdd.xPMinusXR,
      Ecc.CompleteAdd.yQPlusYP]
    simp_all [sub_eq_add_neg]
    constructor
    · have h := h_holds.1
      rw [h_holds.2.2.2.1] at h
      simpa [sub_eq_add_neg] using h
    · have h := h_holds.2.1
      rw [h_holds.2.2.2.2.1] at h
      simpa [sub_eq_add_neg] using h
  completeness := by
    circuit_proof_start [main, constraints, hashOutputCheck, Poseidon.Hash2.constraints,
      Poseidon.Hash2.initial0Check, Poseidon.Hash2.initial1Check,
      Poseidon.Hash2.capacityCheck, Poseidon.Hash2.input0Check,
      Poseidon.Hash2.input1Check, Poseidon.Hash2.hashCheck,
      Poseidon.PadAndAdd.output0Check, Poseidon.PadAndAdd.output1Check,
      Poseidon.PadAndAdd.capacityCheck, Nullifier.constraints, Nullifier.scalarCheck,
      Nullifier.extractCheck, Nullifier.addRow, Ecc.CompleteAdd.main,
      Ecc.CompleteAdd.constraints, Ecc.CompleteAdd.poly1, Ecc.CompleteAdd.poly2,
      Ecc.CompleteAdd.poly3a, Ecc.CompleteAdd.poly3b, Ecc.CompleteAdd.poly3c,
      Ecc.CompleteAdd.poly3d, Ecc.CompleteAdd.poly4a, Ecc.CompleteAdd.poly4b,
      Ecc.CompleteAdd.poly5a, Ecc.CompleteAdd.poly5b, Ecc.CompleteAdd.poly6a,
      Ecc.CompleteAdd.poly6b, Ecc.CompleteAdd.nonexceptionalXR,
      Ecc.CompleteAdd.nonexceptionalYR, Ecc.CompleteAdd.ifAlpha,
      Ecc.CompleteAdd.ifBeta, Ecc.CompleteAdd.ifGamma, Ecc.CompleteAdd.ifDelta,
      Ecc.CompleteAdd.xQMinusXP, Ecc.CompleteAdd.xPMinusXR,
      Ecc.CompleteAdd.yQPlusYP]
    simp_all [sub_eq_add_neg]
    constructor
    · have h := h_spec.1.1
      rw [h_spec.1.2.2.2.1] at h
      simpa [sub_eq_add_neg] using h
    · have h := h_spec.1.2.1
      rw [h_spec.1.2.2.2.2.1] at h
      simpa [sub_eq_add_neg] using h

end NullifierWithHash

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

def constraints (row : Row R) : Prop :=
  Ecc.CompleteAdd.constraints (addRow row)

def main (row : Var Row F) : Circuit F Unit := do
  Ecc.CompleteAdd.main (addRow row)

def circuit : FormalAssertion F Row where
  main
  Spec := constraints
  soundness := by
    circuit_proof_start [main, constraints, addRow, Ecc.CompleteAdd.main,
      Ecc.CompleteAdd.constraints, Ecc.CompleteAdd.poly1, Ecc.CompleteAdd.poly2,
      Ecc.CompleteAdd.poly3a, Ecc.CompleteAdd.poly3b, Ecc.CompleteAdd.poly3c,
      Ecc.CompleteAdd.poly3d, Ecc.CompleteAdd.poly4a, Ecc.CompleteAdd.poly4b,
      Ecc.CompleteAdd.poly5a, Ecc.CompleteAdd.poly5b, Ecc.CompleteAdd.poly6a,
      Ecc.CompleteAdd.poly6b, Ecc.CompleteAdd.nonexceptionalXR,
      Ecc.CompleteAdd.nonexceptionalYR, Ecc.CompleteAdd.ifAlpha,
      Ecc.CompleteAdd.ifBeta, Ecc.CompleteAdd.ifGamma, Ecc.CompleteAdd.ifDelta,
      Ecc.CompleteAdd.xQMinusXP, Ecc.CompleteAdd.xPMinusXR,
      Ecc.CompleteAdd.yQPlusYP]
    simp_all [sub_eq_add_neg]
  completeness := by
    circuit_proof_start [main, constraints, addRow, Ecc.CompleteAdd.main,
      Ecc.CompleteAdd.constraints, Ecc.CompleteAdd.poly1, Ecc.CompleteAdd.poly2,
      Ecc.CompleteAdd.poly3a, Ecc.CompleteAdd.poly3b, Ecc.CompleteAdd.poly3c,
      Ecc.CompleteAdd.poly3d, Ecc.CompleteAdd.poly4a, Ecc.CompleteAdd.poly4b,
      Ecc.CompleteAdd.poly5a, Ecc.CompleteAdd.poly5b, Ecc.CompleteAdd.poly6a,
      Ecc.CompleteAdd.poly6b, Ecc.CompleteAdd.nonexceptionalXR,
      Ecc.CompleteAdd.nonexceptionalYR, Ecc.CompleteAdd.ifAlpha,
      Ecc.CompleteAdd.ifBeta, Ecc.CompleteAdd.ifGamma, Ecc.CompleteAdd.ifDelta,
      Ecc.CompleteAdd.xQMinusXP, Ecc.CompleteAdd.xPMinusXR,
      Ecc.CompleteAdd.yQPlusYP]
    simp_all [sub_eq_add_neg]

end SpendAuth

end Gadget
end Orchard
