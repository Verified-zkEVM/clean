import Clean.Circuit
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

end Merkle

end Sinsemilla
end Orchard
