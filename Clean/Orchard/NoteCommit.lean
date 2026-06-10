import Clean.Circuit
import Clean.Utils.Tactics
import Clean.Utils.Tactics.ProvableStructDeriving

/-!
# Orchard note commitment gates

Clean approximations of Orchard `NoteCommit` arithmetic gates.

Reference:
`orchard@0.14.0/src/circuit/note_commit.rs`
- `NoteCommit MessagePiece b`
- `NoteCommit MessagePiece e`
- `NoteCommit input value`

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

end NoteCommit
end Orchard
