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

end Sinsemilla
end Orchard
