import Clean.Circuit
import Clean.Orchard.Ecc
import Clean.Utils.Tactics
import Clean.Utils.Tactics.ProvableStructDeriving

/-!
# Orchard Sinsemilla gates

Clean approximations of Sinsemilla custom arithmetic gates.

References:
`halo2@halo2_gadgets-0.5.0/halo2_gadgets/src/ecc/chip/mul/incomplete.rs`
- `DoubleAndAdd::x_r`
- `DoubleAndAdd::Y_A`

`halo2@halo2_gadgets-0.5.0/halo2_gadgets/src/sinsemilla/chip.rs`
- `Initial y_Q`
- `Sinsemilla gate`

These gadgets model the arithmetic constraints, not the Halo2 selector, fixed-column,
lookup, or row-layout machinery.
-/

namespace Orchard
namespace Sinsemilla

variable {F : Type} [Field F]

structure DoubleAndAddRow (F : Type) where
  xA : F
  xP : F
  lambda1 : F
  lambda2 : F
deriving ProvableStruct

namespace DoubleAndAdd

variable {R : Type} [Zero R] [Add R] [Sub R] [Mul R]

def xR (row : DoubleAndAddRow R) : R :=
  row.lambda1 * row.lambda1 - row.xA - row.xP

def yA (row : DoubleAndAddRow R) : R :=
  (row.lambda1 + row.lambda2) * (row.xA - xR row)

end DoubleAndAdd

namespace InitialYQ

structure Row (F : Type) where
  yQ : F
  doubleAndAdd : DoubleAndAddRow F
deriving ProvableStruct

def poly (row : Row F) : F :=
  2 * row.yQ - DoubleAndAdd.yA row.doubleAndAdd

def main (row : Var Row F) : Circuit F Unit := do
  assertZero (2 * row.yQ - DoubleAndAdd.yA row.doubleAndAdd)

def circuit : FormalAssertion F Row where
  main
  Spec row := poly row = 0
  soundness := by
    circuit_proof_start [main, poly, DoubleAndAdd.yA, DoubleAndAdd.xR]
    simp_all [sub_eq_add_neg]
  completeness := by
    circuit_proof_start [main, poly, DoubleAndAdd.yA, DoubleAndAdd.xR]
    simp_all [sub_eq_add_neg]

end InitialYQ

/-!
`hash_to_point` initial-`Q` wiring.

Reference:
`halo2@halo2_gadgets-0.5.0/halo2_gadgets/src/sinsemilla/chip/hash_to_point.rs`
- `public_q_initialization`
- `private_q_initialization`

Both source paths assign/copy `x_Q` into the initial accumulator `x_A`, provide `y_Q`
to the `Initial y_Q` gate, and rely on that gate to constrain the first doubled
accumulator. This assertion records the copy/equality wiring around `InitialYQ.circuit`;
whether `y_Q` came from a fixed column or the previous advice row is a Halo2 layout
detail outside this approximation.
-/
namespace InitWiring

variable {R : Type} [Zero R] [Add R] [Sub R] [Mul R] [OfNat R 2]

structure Row (F : Type) where
  qX : F
  qY : F
  init : InitialYQ.Row F
deriving ProvableStruct

def xCheck (row : Row R) : R :=
  row.init.doubleAndAdd.xA - row.qX

def yCheck (row : Row R) : R :=
  row.init.yQ - row.qY

def initPoly (row : Row R) : R :=
  2 * row.init.yQ - DoubleAndAdd.yA row.init.doubleAndAdd

def constraints (row : Row R) : Prop :=
  initPoly row = 0 ∧ xCheck row = 0 ∧ yCheck row = 0

def main (row : Var Row F) : Circuit F Unit := do
  assertZero (initPoly row)
  assertZero (xCheck row)
  assertZero (yCheck row)

def circuit : FormalAssertion F Row where
  main
  Spec := constraints
  soundness := by
    circuit_proof_start [main, constraints, xCheck, yCheck, initPoly,
      DoubleAndAdd.yA, DoubleAndAdd.xR]
    simp_all [sub_eq_add_neg]
  completeness := by
    circuit_proof_start [main, constraints, xCheck, yCheck, initPoly,
      DoubleAndAdd.yA, DoubleAndAdd.xR]
    simp_all [sub_eq_add_neg]

end InitWiring

namespace Gate

variable {R : Type} [Zero R] [One R] [Add R] [Sub R] [Mul R] [OfNat R 2] [OfNat R 4]

structure Row (F : Type) where
  qS2 : F
  cur : DoubleAndAddRow F
  next : DoubleAndAddRow F
deriving ProvableStruct

def qS3 (row : Row R) : R :=
  row.qS2 * (row.qS2 - 1)

def secantLine (row : Row R) : R :=
  row.cur.lambda2 * row.cur.lambda2 -
    (row.next.xA + DoubleAndAdd.xR row.cur + row.cur.xA)

def yCheck (row : Row R) : R :=
  let lhs := 4 * row.cur.lambda2 * (row.cur.xA - row.next.xA)
  let rhs :=
    2 * DoubleAndAdd.yA row.cur +
      (2 - qS3 row) * DoubleAndAdd.yA row.next +
      qS3 row * 2 * row.next.lambda1
  lhs - rhs

def constraints (row : Row R) : Prop :=
  secantLine row = 0 ∧ yCheck row = 0

def main (row : Var Row F) : Circuit F Unit := do
  assertZero (secantLine row)
  assertZero (yCheck row)

def circuit : FormalAssertion F Row where
  main
  Spec := constraints
  soundness := by
    circuit_proof_start [main, constraints, secantLine, yCheck, qS3,
      DoubleAndAdd.yA, DoubleAndAdd.xR]
    simp_all [sub_eq_add_neg]
  completeness := by
    circuit_proof_start [main, constraints, secantLine, yCheck, qS3,
      DoubleAndAdd.yA, DoubleAndAdd.xR]
    simp_all [sub_eq_add_neg]

end Gate

/-!
Sinsemilla commitment output wiring.

Reference:
`halo2@halo2_gadgets-0.5.0/halo2_gadgets/src/sinsemilla.rs`
- `CommitDomain::commit`
- `CommitDomain::short_commit`

The source computes a hash point `M`, a fixed-base blinding factor `[r] R`, and then
returns `M + [r] R`. `short_commit` extracts the x-coordinate from that commitment. The
hash point and blinding factor are explicit row values here; their internal arithmetic is
represented by the lower-level Sinsemilla and fixed-base scalar-multiplication assertions.
-/
namespace Commit

variable {R : Type} [Zero R] [One R] [Add R] [Sub R] [Mul R] [OfNat R 2] [OfNat R 3]

structure Row (F : Type) where
  hashX : F
  hashY : F
  blindX : F
  blindY : F
  commitmentX : F
  commitmentY : F
  lambda : F
  alpha : F
  beta : F
  gamma : F
  delta : F
deriving ProvableStruct

def addRow (row : Row R) : Ecc.CompleteAddRow R where
  p := { x := row.hashX, y := row.hashY }
  q := { x := row.blindX, y := row.blindY }
  r := { x := row.commitmentX, y := row.commitmentY }
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

end Commit

namespace ShortCommit

variable {R : Type} [Zero R] [One R] [Add R] [Sub R] [Mul R] [OfNat R 2] [OfNat R 3]

structure Row (F : Type) where
  commit : Commit.Row F
  extracted : F
deriving ProvableStruct

def extractCheck (row : Row R) : R :=
  row.commit.commitmentX - row.extracted

def constraints (row : Row R) : Prop :=
  Commit.constraints row.commit ∧ extractCheck row = 0

def main (row : Var Row F) : Circuit F Unit := do
  Commit.main row.commit
  assertZero (extractCheck row)

def circuit : FormalAssertion F Row where
  main
  Spec := constraints
  soundness := by
    circuit_proof_start [main, constraints, extractCheck, Commit.main,
      Commit.constraints, Commit.addRow, Ecc.CompleteAdd.main, Ecc.CompleteAdd.constraints,
      Ecc.CompleteAdd.poly1, Ecc.CompleteAdd.poly2, Ecc.CompleteAdd.poly3a,
      Ecc.CompleteAdd.poly3b, Ecc.CompleteAdd.poly3c, Ecc.CompleteAdd.poly3d,
      Ecc.CompleteAdd.poly4a, Ecc.CompleteAdd.poly4b, Ecc.CompleteAdd.poly5a,
      Ecc.CompleteAdd.poly5b, Ecc.CompleteAdd.poly6a, Ecc.CompleteAdd.poly6b,
      Ecc.CompleteAdd.nonexceptionalXR, Ecc.CompleteAdd.nonexceptionalYR,
      Ecc.CompleteAdd.ifAlpha, Ecc.CompleteAdd.ifBeta, Ecc.CompleteAdd.ifGamma,
      Ecc.CompleteAdd.ifDelta, Ecc.CompleteAdd.xQMinusXP, Ecc.CompleteAdd.xPMinusXR,
      Ecc.CompleteAdd.yQPlusYP]
    simp_all [sub_eq_add_neg]
  completeness := by
    circuit_proof_start [main, constraints, extractCheck, Commit.main,
      Commit.constraints, Commit.addRow, Ecc.CompleteAdd.main, Ecc.CompleteAdd.constraints,
      Ecc.CompleteAdd.poly1, Ecc.CompleteAdd.poly2, Ecc.CompleteAdd.poly3a,
      Ecc.CompleteAdd.poly3b, Ecc.CompleteAdd.poly3c, Ecc.CompleteAdd.poly3d,
      Ecc.CompleteAdd.poly4a, Ecc.CompleteAdd.poly4b, Ecc.CompleteAdd.poly5a,
      Ecc.CompleteAdd.poly5b, Ecc.CompleteAdd.poly6a, Ecc.CompleteAdd.poly6b,
      Ecc.CompleteAdd.nonexceptionalXR, Ecc.CompleteAdd.nonexceptionalYR,
      Ecc.CompleteAdd.ifAlpha, Ecc.CompleteAdd.ifBeta, Ecc.CompleteAdd.ifGamma,
      Ecc.CompleteAdd.ifDelta, Ecc.CompleteAdd.xQMinusXP, Ecc.CompleteAdd.xPMinusXR,
      Ecc.CompleteAdd.yQPlusYP]
    simp_all [sub_eq_add_neg]

end ShortCommit

/-!
Reference:
`halo2@halo2_gadgets-0.5.0/halo2_gadgets/src/sinsemilla/merkle/chip.rs`
- `Decomposition check`
- `MerkleInstructions::hash_layer`

This ports the MerkleCRH decomposition gate that connects the three Sinsemilla message
pieces `a`, `b`, `c` to `(l, left, right)`.
-/

namespace Merkle

structure DecompositionRow (F : Type) where
  aWhole : F
  bWhole : F
  cWhole : F
  leftNode : F
  rightNode : F
  z1A : F
  z1B : F
  b1 : F
  b2 : F
  lWhole : F
deriving ProvableStruct

variable {R : Type} [Zero R] [One R] [Add R] [Sub R] [Mul R]
  [OfNat R (2 ^ 5)] [OfNat R (2 ^ 10)] [OfNat R (2 ^ 240)]

def twoPow5 : R := OfNat.ofNat (2 ^ 5)

def twoPow10 : R := OfNat.ofNat (2 ^ 10)

def twoPow240 : R := OfNat.ofNat (2 ^ 240)

def a0 (row : DecompositionRow R) : R :=
  row.aWhole - row.z1A * twoPow10

def b1B2Check (row : DecompositionRow R) : R :=
  row.z1B - (row.b1 + row.b2 * twoPow5)

def b0 (row : DecompositionRow R) : R :=
  row.bWhole - row.z1B * twoPow10

def leftCheck (row : DecompositionRow R) : R :=
  let reconstructed := row.z1A + (b0 row + row.b1 * twoPow10) * twoPow240
  reconstructed - row.leftNode

def rightCheck (row : DecompositionRow R) : R :=
  row.b2 + row.cWhole * twoPow5 - row.rightNode

def constraints (row : DecompositionRow R) : Prop :=
  a0 row - row.lWhole = 0 ∧
  leftCheck row = 0 ∧
  rightCheck row = 0 ∧
  b1B2Check row = 0

def main (row : Var DecompositionRow F) : Circuit F Unit := do
  assertZero (a0 row - row.lWhole)
  assertZero (leftCheck row)
  assertZero (rightCheck row)
  assertZero (b1B2Check row)

def circuit : FormalAssertion F DecompositionRow where
  main
  Spec := constraints
  soundness := by
    circuit_proof_start [main, constraints, a0, leftCheck, rightCheck, b1B2Check,
      b0, twoPow5, twoPow10, twoPow240]
    simp_all [sub_eq_add_neg]
  completeness := by
    circuit_proof_start [main, constraints, a0, leftCheck, rightCheck, b1B2Check,
      b0, twoPow5, twoPow10, twoPow240]
    simp_all [sub_eq_add_neg]

/-!
`hash_layer` source-level wiring.

Reference:
`halo2@halo2_gadgets-0.5.0/halo2_gadgets/src/sinsemilla/merkle/chip.rs`
- `MerkleInstructions::hash_layer`

The Rust gadget builds message pieces `a`, `b`, and `c`, calls
`SinsemillaChip::hash_to_point`, extracts the x-coordinate, and assigns the
decomposition row above from the message pieces, running-sum endpoints, and short
subpieces. The variable-length `hash_to_point` loop is represented by an explicit
`computedHash` row value.
-/
namespace Wiring

structure Row (F : Type) where
  decomposition : DecompositionRow F
  computedHash : F
  hash : F
deriving ProvableStruct

def hashCheck (row : Row R) : R :=
  row.computedHash - row.hash

def constraints (row : Row R) : Prop :=
  Merkle.constraints row.decomposition ∧ hashCheck row = 0

def main (row : Var Row F) : Circuit F Unit := do
  assertZero (Merkle.a0 row.decomposition - row.decomposition.lWhole)
  assertZero (Merkle.leftCheck row.decomposition)
  assertZero (Merkle.rightCheck row.decomposition)
  assertZero (Merkle.b1B2Check row.decomposition)
  assertZero (hashCheck row)

def circuit : FormalAssertion F Row where
  main
  Spec := constraints
  soundness := by
    circuit_proof_start [main, constraints, hashCheck, Merkle.constraints, Merkle.a0,
      Merkle.leftCheck, Merkle.rightCheck, Merkle.b1B2Check, Merkle.b0,
      Merkle.twoPow5, Merkle.twoPow10, Merkle.twoPow240]
    simp_all [sub_eq_add_neg]
  completeness := by
    circuit_proof_start [main, constraints, hashCheck, Merkle.constraints, Merkle.a0,
      Merkle.leftCheck, Merkle.rightCheck, Merkle.b1B2Check, Merkle.b0,
      Merkle.twoPow5, Merkle.twoPow10, Merkle.twoPow240]
    simp_all [sub_eq_add_neg]

end Wiring

/-!
Merkle-path per-layer wiring.

Reference:
`halo2@halo2_gadgets-0.5.0/halo2_gadgets/src/sinsemilla/merkle.rs`
- `MerklePath::calculate_root`

For each layer, the source conditionally swaps `(node, sibling)` according to the
little-endian position bit, then hashes `(left, right)` with `hash_layer`. This assertion
models one such layer. Repeating it outside this assertion models the full path.
-/
namespace PathStep

structure Row (F : Type) where
  node : F
  sibling : F
  posBit : F
  left : F
  right : F
  layer : Wiring.Row F
  nextNode : F
deriving ProvableStruct

variable {R : Type} [Zero R] [One R] [Add R] [Sub R] [Mul R]
  [OfNat R (2 ^ 5)] [OfNat R (2 ^ 10)] [OfNat R (2 ^ 240)]

def boolPoly (x : R) : R :=
  x * (x - 1)

def ternary (choice ifTrue ifFalse : R) : R :=
  choice * ifTrue + (1 - choice) * ifFalse

def leftCheck (row : Row R) : R :=
  row.left - ternary row.posBit row.sibling row.node

def rightCheck (row : Row R) : R :=
  row.right - ternary row.posBit row.node row.sibling

def layerLeftCheck (row : Row R) : R :=
  row.layer.decomposition.leftNode - row.left

def layerRightCheck (row : Row R) : R :=
  row.layer.decomposition.rightNode - row.right

def nextCheck (row : Row R) : R :=
  row.layer.hash - row.nextNode

def constraints (row : Row R) : Prop :=
  boolPoly row.posBit = 0 ∧
    leftCheck row = 0 ∧
    rightCheck row = 0 ∧
    Wiring.constraints row.layer ∧
    layerLeftCheck row = 0 ∧
    layerRightCheck row = 0 ∧
    nextCheck row = 0

def main (row : Var Row F) : Circuit F Unit := do
  assertZero (boolPoly row.posBit)
  assertZero (leftCheck row)
  assertZero (rightCheck row)
  assertZero (Merkle.a0 row.layer.decomposition - row.layer.decomposition.lWhole)
  assertZero (Merkle.leftCheck row.layer.decomposition)
  assertZero (Merkle.rightCheck row.layer.decomposition)
  assertZero (Merkle.b1B2Check row.layer.decomposition)
  assertZero (Wiring.hashCheck row.layer)
  assertZero (layerLeftCheck row)
  assertZero (layerRightCheck row)
  assertZero (nextCheck row)

def circuit : FormalAssertion F Row where
  main
  Spec := constraints
  soundness := by
    circuit_proof_start [main, constraints, leftCheck, rightCheck, layerLeftCheck,
      layerRightCheck, nextCheck, ternary, boolPoly,
      Wiring.constraints, Wiring.hashCheck, Merkle.constraints, Merkle.a0,
      Merkle.leftCheck, Merkle.rightCheck, Merkle.b1B2Check, Merkle.b0,
      Merkle.twoPow5, Merkle.twoPow10, Merkle.twoPow240]
    simp_all [sub_eq_add_neg]
  completeness := by
    circuit_proof_start [main, constraints, leftCheck, rightCheck, layerLeftCheck,
      layerRightCheck, nextCheck, ternary, boolPoly,
      Wiring.constraints, Wiring.hashCheck, Merkle.constraints, Merkle.a0,
      Merkle.leftCheck, Merkle.rightCheck, Merkle.b1B2Check, Merkle.b0,
      Merkle.twoPow5, Merkle.twoPow10, Merkle.twoPow240]
    simp_all [sub_eq_add_neg]

end PathStep

end Merkle

end Sinsemilla
end Orchard
