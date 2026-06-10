import Clean.Circuit
import Clean.Orchard.NoteCommit
import Clean.Utils.Tactics
import Clean.Utils.Tactics.ProvableStructDeriving

/-!
# Orchard scalar multiplication gates

Clean approximations of direct scalar-multiplication custom gates from `halo2_gadgets`.

References:
`halo2@halo2_gadgets-0.5.0/halo2_gadgets/src/ecc/chip/mul.rs`
- `LSB check`

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
