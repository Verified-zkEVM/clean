import Clean.Circuit
import Clean.Orchard.NoteCommit
import Clean.Orchard.Sinsemilla
import Clean.Utils.Tactics
import Clean.Utils.Tactics.ProvableStructDeriving

/-!
# Orchard scalar multiplication gates

Clean approximations of direct scalar-multiplication custom gates from `halo2_gadgets`.

References:
`halo2@halo2_gadgets-0.5.0/halo2_gadgets/src/ecc/chip/mul.rs`
- `LSB check`

`halo2@halo2_gadgets-0.5.0/halo2_gadgets/src/ecc/chip/mul/incomplete.rs`
- `q_mul_1 == 1 checks`
- shared `for_loop` constraints for `q_mul_2 == 1 checks` and `q_mul_3 == 1 checks`

`halo2@halo2_gadgets-0.5.0/halo2_gadgets/src/ecc/chip/mul/complete.rs`
- `Decompose scalar for complete bits of variable-base mul`

`halo2@halo2_gadgets-0.5.0/halo2_gadgets/src/ecc/chip/mul_fixed/short.rs`
- `Short fixed-base mul gate`

These assertions model the enabled gate polynomials, not row rotations, selectors,
lookups, fixed-base tables, or copy constraints around the gates.
-/

namespace Orchard
namespace ScalarMul

variable {F : Type} [Field F]

variable {R : Type} [Zero R] [One R] [Add R] [Sub R] [Mul R] [OfNat R 2]

def ternary (choice ifTrue ifFalse : R) : R :=
  choice * ifTrue + (1 - choice) * ifFalse

namespace VarBaseLSB

structure Row (F : Type) where
  z1 : F
  z0 : F
  xP : F
  yP : F
  baseX : F
  baseY : F
deriving ProvableStruct

def lsb (row : Row R) : R :=
  row.z0 - row.z1 * 2

def lsbX (row : Row R) : R :=
  ternary (lsb row) row.xP (row.xP - row.baseX)

def lsbY (row : Row R) : R :=
  ternary (lsb row) row.yP (row.yP + row.baseY)

def constraints (row : Row R) : Prop :=
  NoteCommit.boolPoly (lsb row) = 0 ∧ lsbX row = 0 ∧ lsbY row = 0

def main (row : Var Row F) : Circuit F Unit := do
  assertZero (NoteCommit.boolPoly (lsb row))
  assertZero (lsbX row)
  assertZero (lsbY row)

def circuit : FormalAssertion F Row where
  main
  Spec := constraints
  soundness := by
    circuit_proof_start [main, constraints, NoteCommit.boolPoly, lsb, lsbX, lsbY,
      ternary]
    simp_all [sub_eq_add_neg]
  completeness := by
    circuit_proof_start [main, constraints, NoteCommit.boolPoly, lsb, lsbX, lsbY,
      ternary]
    simp_all [sub_eq_add_neg]

end VarBaseLSB

namespace VarBaseCompleteBit

structure Row (F : Type) where
  zPrev : F
  zNext : F
  baseY : F
  yP : F
deriving ProvableStruct

def bit (row : Row R) : R :=
  row.zNext - 2 * row.zPrev

def ySwitch (row : Row R) : R :=
  ternary (bit row) (row.baseY - row.yP) (row.baseY + row.yP)

def constraints (row : Row R) : Prop :=
  NoteCommit.boolPoly (bit row) = 0 ∧ ySwitch row = 0

def main (row : Var Row F) : Circuit F Unit := do
  assertZero (NoteCommit.boolPoly (bit row))
  assertZero (ySwitch row)

def circuit : FormalAssertion F Row where
  main
  Spec := constraints
  soundness := by
    circuit_proof_start [main, constraints, NoteCommit.boolPoly, bit, ySwitch,
      ternary]
    simp_all [sub_eq_add_neg]
  completeness := by
    circuit_proof_start [main, constraints, NoteCommit.boolPoly, bit, ySwitch,
      ternary]
    simp_all [sub_eq_add_neg]

end VarBaseCompleteBit

namespace VarBaseIncomplete

/- The Rust gate uses `y_a = Y_A / 2`. These constraints multiply those
   equations by `2`, avoiding a division operation while preserving the Pallas
   gate's zero set. -/
def yADouble (row : Sinsemilla.DoubleAndAddRow R) : R :=
  Sinsemilla.DoubleAndAdd.yA row

namespace Init

structure Row (F : Type) where
  yAWitnessed : F
  next : Sinsemilla.DoubleAndAddRow F
deriving ProvableStruct

def poly (row : Row R) : R :=
  2 * row.yAWitnessed - yADouble row.next

def main (row : Var Row F) : Circuit F Unit := do
  assertZero (poly row)

def circuit : FormalAssertion F Row where
  main
  Spec row := poly row = 0
  soundness := by
    circuit_proof_start [main, poly, yADouble, Sinsemilla.DoubleAndAdd.yA,
      Sinsemilla.DoubleAndAdd.xR]
    simp_all [sub_eq_add_neg]
  completeness := by
    circuit_proof_start [main, poly, yADouble, Sinsemilla.DoubleAndAdd.yA,
      Sinsemilla.DoubleAndAdd.xR]
    simp_all [sub_eq_add_neg]

end Init

namespace Loop

structure Row (F : Type) where
  zCur : F
  zPrev : F
  cur : Sinsemilla.DoubleAndAddRow F
  xANext : F
  yPCur : F
  yANextDouble : F
deriving ProvableStruct

def bit (row : Row R) : R :=
  row.zCur - row.zPrev * 2

def gradient1 (row : Row R) : R :=
  2 * row.cur.lambda1 * (row.cur.xA - row.cur.xP) - yADouble row.cur +
    2 * ((bit row * 2 - 1) * row.yPCur)

def secantLine (row : Row R) : R :=
  row.cur.lambda2 * row.cur.lambda2 - row.xANext -
    Sinsemilla.DoubleAndAdd.xR row.cur - row.cur.xA

def gradient2 (row : Row R) : R :=
  2 * row.cur.lambda2 * (row.cur.xA - row.xANext) - yADouble row.cur - row.yANextDouble

def constraints (row : Row R) : Prop :=
  NoteCommit.boolPoly (bit row) = 0 ∧
    gradient1 row = 0 ∧
    secantLine row = 0 ∧
    gradient2 row = 0

def main (row : Var Row F) : Circuit F Unit := do
  assertZero (NoteCommit.boolPoly (bit row))
  assertZero (gradient1 row)
  assertZero (secantLine row)
  assertZero (gradient2 row)

def circuit : FormalAssertion F Row where
  main
  Spec := constraints
  soundness := by
    circuit_proof_start [main, constraints, NoteCommit.boolPoly, bit, gradient1,
      secantLine, gradient2, yADouble, Sinsemilla.DoubleAndAdd.yA, Sinsemilla.DoubleAndAdd.xR]
    simp_all [sub_eq_add_neg]
  completeness := by
    circuit_proof_start [main, constraints, NoteCommit.boolPoly, bit, gradient1,
      secantLine, gradient2, yADouble, Sinsemilla.DoubleAndAdd.yA, Sinsemilla.DoubleAndAdd.xR]
    simp_all [sub_eq_add_neg]

end Loop

namespace MainLoop

structure Row (F : Type) extends Loop.Row F where
  xPNext : F
  yPNext : F
deriving ProvableStruct

def xPCheck (row : Row R) : R :=
  row.cur.xP - row.xPNext

def yPCheck (row : Row R) : R :=
  row.yPCur - row.yPNext

def constraints (row : Row R) : Prop :=
  xPCheck row = 0 ∧ yPCheck row = 0 ∧ Loop.constraints row.toRow

def main (row : Var Row F) : Circuit F Unit := do
  assertZero (xPCheck row)
  assertZero (yPCheck row)
  Loop.main row.toRow

def circuit : FormalAssertion F Row where
  main
  Spec := constraints
  soundness := by
    circuit_proof_start [main, constraints, xPCheck, yPCheck, Loop.main,
      Loop.constraints, NoteCommit.boolPoly, Loop.bit, Loop.gradient1,
      Loop.secantLine, Loop.gradient2, yADouble, Sinsemilla.DoubleAndAdd.yA,
      Sinsemilla.DoubleAndAdd.xR]
    simp_all [sub_eq_add_neg]
  completeness := by
    circuit_proof_start [main, constraints, xPCheck, yPCheck, Loop.main,
      Loop.constraints, NoteCommit.boolPoly, Loop.bit, Loop.gradient1,
      Loop.secantLine, Loop.gradient2, yADouble, Sinsemilla.DoubleAndAdd.yA,
      Sinsemilla.DoubleAndAdd.xR]
    simp_all [sub_eq_add_neg]

end MainLoop

end VarBaseIncomplete

namespace FixedShort

structure Row (F : Type) where
  yP : F
  yA : F
  lastWindow : F
  sign : F
deriving ProvableStruct

def signCheck (row : Row R) : R :=
  row.sign * row.sign - 1

def yCheck (row : Row R) : R :=
  (row.yP - row.yA) * (row.yP + row.yA)

def negationCheck (row : Row R) : R :=
  row.sign * row.yP - row.yA

def constraints (row : Row R) : Prop :=
  NoteCommit.boolPoly row.lastWindow = 0 ∧
    signCheck row = 0 ∧
    yCheck row = 0 ∧
    negationCheck row = 0

def main (row : Var Row F) : Circuit F Unit := do
  assertZero (NoteCommit.boolPoly row.lastWindow)
  assertZero (signCheck row)
  assertZero (yCheck row)
  assertZero (negationCheck row)

def circuit : FormalAssertion F Row where
  main
  Spec := constraints
  soundness := by
    circuit_proof_start [main, constraints, NoteCommit.boolPoly, signCheck, yCheck,
      negationCheck]
    simp_all [sub_eq_add_neg]
  completeness := by
    circuit_proof_start [main, constraints, NoteCommit.boolPoly, signCheck, yCheck,
      negationCheck]
    simp_all [sub_eq_add_neg]

end FixedShort

end ScalarMul
end Orchard
