import Clean.Circuit
import Clean.Orchard.Ecc
import Clean.Utils.Tactics
import Clean.Utils.Tactics.ProvableStructDeriving

/-!
# Orchard gadget composition assertions

Clean approximations of source-level Orchard circuit gadget wiring.

References:
`orchard@0.14.0/src/circuit/gadget.rs`
- `value_commit_orchard`
- `derive_nullifier`

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

end Gadget
end Orchard
