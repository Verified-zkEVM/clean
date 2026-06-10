import Clean.Circuit
import Clean.Utils.Tactics
import Clean.Utils.Tactics.ProvableStructDeriving

/-!
# Orchard note commitment gates

Clean approximations of Orchard `NoteCommit` arithmetic gates.

Reference:
`orchard@0.14.0/src/circuit/note_commit.rs`
- `NoteCommit MessagePiece b`
- `NoteCommit MessagePiece d`
- `NoteCommit MessagePiece e`
- `NoteCommit MessagePiece g`
- `NoteCommit MessagePiece h`
- `NoteCommit input g_d`
- `NoteCommit input pk_d`
- `NoteCommit input rho`
- `NoteCommit input psi`
- `NoteCommit input value`
- `y coordinate checks`

These assertions model the enabled Halo2 custom-gate polynomials, not selector,
rotation, column-layout, lookup, or copy-constraint machinery. Range constraints named in
the Rust comments are provided outside these gates in the source circuit, so they are not
duplicated here.
-/

namespace Orchard
namespace NoteCommit

variable {F : Type} [Field F]

variable {R : Type} [Zero R] [One R] [Add R] [Sub R] [Mul R]

def boolPoly (x : R) : R :=
  x * (x - 1)

def tP [OfNat R 45560315531419706090280762371685220353] : R :=
  OfNat.ofNat 45560315531419706090280762371685220353

namespace DecomposeB

variable [OfNat R 16] [OfNat R 32] [OfNat R 64]

structure Row (F : Type) where
  b : F
  b0 : F
  b1 : F
  b2 : F
  b3 : F
deriving ProvableStruct

def decomposition (row : Row R) : R :=
  row.b - (row.b0 + row.b1 * 16 + row.b2 * 32 + row.b3 * 64)

def constraints (row : Row R) : Prop :=
  boolPoly row.b1 = 0 ∧ boolPoly row.b2 = 0 ∧ decomposition row = 0

def main (row : Var Row F) : Circuit F Unit := do
  assertZero (boolPoly row.b1)
  assertZero (boolPoly row.b2)
  assertZero (decomposition row)

def circuit : FormalAssertion F Row where
  main
  Spec := constraints
  soundness := by
    circuit_proof_start [main, constraints, boolPoly, decomposition]
    simp_all [sub_eq_add_neg]
  completeness := by
    circuit_proof_start [main, constraints, boolPoly, decomposition]
    simp_all [sub_eq_add_neg]

end DecomposeB

namespace DecomposeD

variable [OfNat R 2] [OfNat R 4] [OfNat R 1024]

structure Row (F : Type) where
  d : F
  d0 : F
  d1 : F
  d2 : F
  d3 : F
deriving ProvableStruct

def decomposition (row : Row R) : R :=
  row.d - (row.d0 + row.d1 * 2 + row.d2 * 4 + row.d3 * 1024)

def constraints (row : Row R) : Prop :=
  boolPoly row.d0 = 0 ∧ boolPoly row.d1 = 0 ∧ decomposition row = 0

def main (row : Var Row F) : Circuit F Unit := do
  assertZero (boolPoly row.d0)
  assertZero (boolPoly row.d1)
  assertZero (decomposition row)

def circuit : FormalAssertion F Row where
  main
  Spec := constraints
  soundness := by
    circuit_proof_start [main, constraints, boolPoly, decomposition]
    simp_all [sub_eq_add_neg]
  completeness := by
    circuit_proof_start [main, constraints, boolPoly, decomposition]
    simp_all [sub_eq_add_neg]

end DecomposeD

namespace DecomposeE

variable [OfNat R 64]

structure Row (F : Type) where
  e : F
  e0 : F
  e1 : F
deriving ProvableStruct

def decomposition (row : Row R) : R :=
  row.e - (row.e0 + row.e1 * 64)

def main (row : Var Row F) : Circuit F Unit := do
  assertZero (decomposition row)

def circuit : FormalAssertion F Row where
  main
  Spec row := decomposition row = 0
  soundness := by
    circuit_proof_start [main, decomposition]
    simp_all [sub_eq_add_neg]
  completeness := by
    circuit_proof_start [main, decomposition]
    simp_all [sub_eq_add_neg]

end DecomposeE

namespace DecomposeG

variable [OfNat R 2] [OfNat R 1024]

structure Row (F : Type) where
  g : F
  g0 : F
  g1 : F
  g2 : F
deriving ProvableStruct

def decomposition (row : Row R) : R :=
  row.g - (row.g0 + row.g1 * 2 + row.g2 * 1024)

def constraints (row : Row R) : Prop :=
  boolPoly row.g0 = 0 ∧ decomposition row = 0

def main (row : Var Row F) : Circuit F Unit := do
  assertZero (boolPoly row.g0)
  assertZero (decomposition row)

def circuit : FormalAssertion F Row where
  main
  Spec := constraints
  soundness := by
    circuit_proof_start [main, constraints, boolPoly, decomposition]
    simp_all [sub_eq_add_neg]
  completeness := by
    circuit_proof_start [main, constraints, boolPoly, decomposition]
    simp_all [sub_eq_add_neg]

end DecomposeG

namespace DecomposeH

variable [OfNat R 32]

structure Row (F : Type) where
  h : F
  h0 : F
  h1 : F
deriving ProvableStruct

def decomposition (row : Row R) : R :=
  row.h - (row.h0 + row.h1 * 32)

def constraints (row : Row R) : Prop :=
  boolPoly row.h1 = 0 ∧ decomposition row = 0

def main (row : Var Row F) : Circuit F Unit := do
  assertZero (boolPoly row.h1)
  assertZero (decomposition row)

def circuit : FormalAssertion F Row where
  main
  Spec := constraints
  soundness := by
    circuit_proof_start [main, constraints, boolPoly, decomposition]
    simp_all [sub_eq_add_neg]
  completeness := by
    circuit_proof_start [main, constraints, boolPoly, decomposition]
    simp_all [sub_eq_add_neg]

end DecomposeH

namespace GdCanonicity

variable [OfNat R (2 ^ 130)] [OfNat R (2 ^ 250)] [OfNat R (2 ^ 254)]
  [OfNat R 45560315531419706090280762371685220353]

structure Row (F : Type) where
  gdX : F
  b0 : F
  b1 : F
  a : F
  aPrime : F
  z13A : F
  z13APrime : F
deriving ProvableStruct

def decomposition (row : Row R) : R :=
  row.a + row.b0 * OfNat.ofNat (2 ^ 250) + row.b1 * OfNat.ofNat (2 ^ 254) - row.gdX

def aPrimeCheck (row : Row R) : R :=
  row.a + OfNat.ofNat (2 ^ 130) - tP - row.aPrime

def constraints (row : Row R) : Prop :=
  decomposition row = 0 ∧
    aPrimeCheck row = 0 ∧
    row.b1 * row.b0 = 0 ∧
    row.b1 * row.z13A = 0 ∧
    row.b1 * row.z13APrime = 0

def main (row : Var Row F) : Circuit F Unit := do
  assertZero (decomposition row)
  assertZero (aPrimeCheck row)
  assertZero (row.b1 * row.b0)
  assertZero (row.b1 * row.z13A)
  assertZero (row.b1 * row.z13APrime)

def circuit : FormalAssertion F Row where
  main
  Spec := constraints
  soundness := by
    circuit_proof_start [main, constraints, decomposition, aPrimeCheck, tP]
    simp_all [sub_eq_add_neg]
  completeness := by
    circuit_proof_start [main, constraints, decomposition, aPrimeCheck, tP]
    simp_all [sub_eq_add_neg]

end GdCanonicity

namespace PkdCanonicity

variable [OfNat R 16] [OfNat R (2 ^ 140)] [OfNat R (2 ^ 254)]
  [OfNat R 45560315531419706090280762371685220353]

structure Row (F : Type) where
  pkdX : F
  b3 : F
  d0 : F
  c : F
  b3CPrime : F
  z13C : F
  z14B3CPrime : F
deriving ProvableStruct

def decomposition (row : Row R) : R :=
  row.b3 + row.c * 16 + row.d0 * OfNat.ofNat (2 ^ 254) - row.pkdX

def b3CPrimeCheck (row : Row R) : R :=
  row.b3 + row.c * 16 + OfNat.ofNat (2 ^ 140) - tP - row.b3CPrime

def constraints (row : Row R) : Prop :=
  decomposition row = 0 ∧
    b3CPrimeCheck row = 0 ∧
    row.d0 * row.z13C = 0 ∧
    row.d0 * row.z14B3CPrime = 0

def main (row : Var Row F) : Circuit F Unit := do
  assertZero (decomposition row)
  assertZero (b3CPrimeCheck row)
  assertZero (row.d0 * row.z13C)
  assertZero (row.d0 * row.z14B3CPrime)

def circuit : FormalAssertion F Row where
  main
  Spec := constraints
  soundness := by
    circuit_proof_start [main, constraints, decomposition, b3CPrimeCheck, tP]
    simp_all [sub_eq_add_neg]
  completeness := by
    circuit_proof_start [main, constraints, decomposition, b3CPrimeCheck, tP]
    simp_all [sub_eq_add_neg]

end PkdCanonicity

namespace ValueCanonicity

variable [OfNat R 256] [OfNat R 288230376151711744]

structure Row (F : Type) where
  value : F
  d2 : F
  d3 : F
  e0 : F
deriving ProvableStruct

def valueCheck (row : Row R) : R :=
  row.d2 + row.d3 * 256 + row.e0 * 288230376151711744 - row.value

def main (row : Var Row F) : Circuit F Unit := do
  assertZero (valueCheck row)

def circuit : FormalAssertion F Row where
  main
  Spec row := valueCheck row = 0
  soundness := by
    circuit_proof_start [main, valueCheck]
    simp_all [sub_eq_add_neg]
  completeness := by
    circuit_proof_start [main, valueCheck]
    simp_all [sub_eq_add_neg]

end ValueCanonicity

namespace RhoCanonicity

variable [OfNat R 16] [OfNat R (2 ^ 140)] [OfNat R (2 ^ 254)]
  [OfNat R 45560315531419706090280762371685220353]

structure Row (F : Type) where
  rho : F
  e1 : F
  g0 : F
  f : F
  e1FPrime : F
  z13F : F
  z14E1FPrime : F
deriving ProvableStruct

def decomposition (row : Row R) : R :=
  row.e1 + row.f * 16 + row.g0 * OfNat.ofNat (2 ^ 254) - row.rho

def e1FPrimeCheck (row : Row R) : R :=
  row.e1 + row.f * 16 + OfNat.ofNat (2 ^ 140) - tP - row.e1FPrime

def constraints (row : Row R) : Prop :=
  decomposition row = 0 ∧
    e1FPrimeCheck row = 0 ∧
    row.g0 * row.z13F = 0 ∧
    row.g0 * row.z14E1FPrime = 0

def main (row : Var Row F) : Circuit F Unit := do
  assertZero (decomposition row)
  assertZero (e1FPrimeCheck row)
  assertZero (row.g0 * row.z13F)
  assertZero (row.g0 * row.z14E1FPrime)

def circuit : FormalAssertion F Row where
  main
  Spec := constraints
  soundness := by
    circuit_proof_start [main, constraints, decomposition, e1FPrimeCheck, tP]
    simp_all [sub_eq_add_neg]
  completeness := by
    circuit_proof_start [main, constraints, decomposition, e1FPrimeCheck, tP]
    simp_all [sub_eq_add_neg]

end RhoCanonicity

namespace PsiCanonicity

variable [OfNat R 512] [OfNat R (2 ^ 130)] [OfNat R (2 ^ 249)] [OfNat R (2 ^ 254)]
  [OfNat R 45560315531419706090280762371685220353]

structure Row (F : Type) where
  psi : F
  h0 : F
  g1 : F
  h1 : F
  g2 : F
  g1G2Prime : F
  z13G : F
  z13G1G2Prime : F
deriving ProvableStruct

def decomposition (row : Row R) : R :=
  row.g1 + row.g2 * 512 + row.h0 * OfNat.ofNat (2 ^ 249) +
    row.h1 * OfNat.ofNat (2 ^ 254) - row.psi

def g1G2PrimeCheck (row : Row R) : R :=
  row.g1 + row.g2 * 512 + OfNat.ofNat (2 ^ 130) - tP - row.g1G2Prime

def constraints (row : Row R) : Prop :=
  decomposition row = 0 ∧
    g1G2PrimeCheck row = 0 ∧
    row.h1 * row.h0 = 0 ∧
    row.h1 * row.z13G = 0 ∧
    row.h1 * row.z13G1G2Prime = 0

def main (row : Var Row F) : Circuit F Unit := do
  assertZero (decomposition row)
  assertZero (g1G2PrimeCheck row)
  assertZero (row.h1 * row.h0)
  assertZero (row.h1 * row.z13G)
  assertZero (row.h1 * row.z13G1G2Prime)

def circuit : FormalAssertion F Row where
  main
  Spec := constraints
  soundness := by
    circuit_proof_start [main, constraints, decomposition, g1G2PrimeCheck, tP]
    simp_all [sub_eq_add_neg]
  completeness := by
    circuit_proof_start [main, constraints, decomposition, g1G2PrimeCheck, tP]
    simp_all [sub_eq_add_neg]

end PsiCanonicity

namespace YCanonicity

variable [OfNat R 2] [OfNat R 1024] [OfNat R (2 ^ 130)] [OfNat R (2 ^ 250)]
  [OfNat R (2 ^ 254)] [OfNat R 45560315531419706090280762371685220353]

structure Row (F : Type) where
  y : F
  lsb : F
  k0 : F
  k2 : F
  k3 : F
  j : F
  z1J : F
  z13J : F
  jPrime : F
  z13JPrime : F
deriving ProvableStruct

def jCheck (row : Row R) : R :=
  row.j - (row.lsb + row.k0 * 2 + row.z1J * 1024)

def yCheck (row : Row R) : R :=
  row.y - (row.j + row.k2 * OfNat.ofNat (2 ^ 250) +
    row.k3 * OfNat.ofNat (2 ^ 254))

def jPrimeCheck (row : Row R) : R :=
  row.j + OfNat.ofNat (2 ^ 130) - tP - row.jPrime

def constraints (row : Row R) : Prop :=
  boolPoly row.k3 = 0 ∧
    jCheck row = 0 ∧
    yCheck row = 0 ∧
    jPrimeCheck row = 0 ∧
    row.k3 * row.k2 = 0 ∧
    row.k3 * row.z13J = 0 ∧
    row.k3 * row.z13JPrime = 0

def main (row : Var Row F) : Circuit F Unit := do
  assertZero (boolPoly row.k3)
  assertZero (jCheck row)
  assertZero (yCheck row)
  assertZero (jPrimeCheck row)
  assertZero (row.k3 * row.k2)
  assertZero (row.k3 * row.z13J)
  assertZero (row.k3 * row.z13JPrime)

def circuit : FormalAssertion F Row where
  main
  Spec := constraints
  soundness := by
    circuit_proof_start [main, constraints, boolPoly, jCheck, yCheck, jPrimeCheck, tP]
    simp_all [sub_eq_add_neg]
  completeness := by
    circuit_proof_start [main, constraints, boolPoly, jCheck, yCheck, jPrimeCheck, tP]
    simp_all [sub_eq_add_neg]

end YCanonicity

end NoteCommit
end Orchard
