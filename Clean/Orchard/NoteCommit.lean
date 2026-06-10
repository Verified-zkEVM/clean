import Clean.Circuit
import Clean.Orchard.Sinsemilla
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
- `gadgets::note_commit`

Most assertions model the enabled Halo2 custom-gate polynomials, not selector, rotation,
column-layout, lookup, or assignment machinery. `Wiring.circuit` additionally models the
copy constraints and output wiring that `gadgets::note_commit` makes explicit. Range
constraints named in the Rust comments are provided outside these gates in the source
circuit, so they are not duplicated here.
-/

namespace Orchard
namespace NoteCommit

variable {F : Type} [Field F]

variable {R : Type} [Zero R] [One R] [Add R] [Sub R] [Mul R]

def boolPoly (x : R) : R :=
  x * (x - 1)

def IsBool (x : R) : Prop :=
  x = 0 ∨ x = 1

private theorem isBool_of_boolPoly_eq_zero {x : F} (h : boolPoly x = 0) : IsBool x := by
  unfold boolPoly at h
  rcases mul_eq_zero.mp h with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (sub_eq_zero.mp h1)

private theorem boolPoly_eq_zero_of_isBool {x : F} (h : IsBool x) : boolPoly x = 0 := by
  rcases h with h | h <;> rw [h] <;> simp [boolPoly]

private theorem mul_eq_zero_of_or {a b : F} (h : a = 0 ∨ b = 0) : a * b = 0 := by
  rcases h with h | h <;> rw [h] <;> simp

private theorem left_eq_of_add_neg_eq_zero {a b : F} (h : a + -b = 0) : a = b :=
  sub_eq_zero.mp (by simpa [sub_eq_add_neg] using h)

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

def Spec (row : Row R) : Prop :=
  IsBool row.b1 ∧
  IsBool row.b2 ∧
  row.b = row.b0 + row.b1 * 16 + row.b2 * 32 + row.b3 * 64

def constraints (row : Row R) : Prop :=
  boolPoly row.b1 = 0 ∧ boolPoly row.b2 = 0 ∧ decomposition row = 0

def main (row : Var Row F) : Circuit F Unit := do
  assertZero (boolPoly row.b1)
  assertZero (boolPoly row.b2)
  assertZero (decomposition row)

def circuit : FormalAssertion F Row where
  main
  Spec := Spec
  soundness := by
    circuit_proof_start [main, Spec, constraints, IsBool, boolPoly, decomposition]
    rcases h_holds with ⟨hb1, hb2, hdec⟩
    exact ⟨isBool_of_boolPoly_eq_zero (by simpa [boolPoly, sub_eq_add_neg] using hb1),
      isBool_of_boolPoly_eq_zero (by simpa [boolPoly, sub_eq_add_neg] using hb2),
      left_eq_of_add_neg_eq_zero hdec⟩
  completeness := by
    circuit_proof_start [main, Spec, constraints, IsBool, boolPoly, decomposition]
    rcases h_spec with ⟨hb1, hb2, hdec⟩
    exact ⟨by simpa [boolPoly, sub_eq_add_neg] using boolPoly_eq_zero_of_isBool hb1,
      by simpa [boolPoly, sub_eq_add_neg] using boolPoly_eq_zero_of_isBool hb2,
      by rw [hdec]; ring⟩

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

def Spec (row : Row R) : Prop :=
  IsBool row.d0 ∧
  IsBool row.d1 ∧
  row.d = row.d0 + row.d1 * 2 + row.d2 * 4 + row.d3 * 1024

def constraints (row : Row R) : Prop :=
  boolPoly row.d0 = 0 ∧ boolPoly row.d1 = 0 ∧ decomposition row = 0

def main (row : Var Row F) : Circuit F Unit := do
  assertZero (boolPoly row.d0)
  assertZero (boolPoly row.d1)
  assertZero (decomposition row)

def circuit : FormalAssertion F Row where
  main
  Spec := Spec
  soundness := by
    circuit_proof_start [main, Spec, constraints, IsBool, boolPoly, decomposition]
    rcases h_holds with ⟨hd0, hd1, hdec⟩
    exact ⟨isBool_of_boolPoly_eq_zero (by simpa [boolPoly, sub_eq_add_neg] using hd0),
      isBool_of_boolPoly_eq_zero (by simpa [boolPoly, sub_eq_add_neg] using hd1),
      left_eq_of_add_neg_eq_zero hdec⟩
  completeness := by
    circuit_proof_start [main, Spec, constraints, IsBool, boolPoly, decomposition]
    rcases h_spec with ⟨hd0, hd1, hdec⟩
    exact ⟨by simpa [boolPoly, sub_eq_add_neg] using boolPoly_eq_zero_of_isBool hd0,
      by simpa [boolPoly, sub_eq_add_neg] using boolPoly_eq_zero_of_isBool hd1,
      by rw [hdec]; ring⟩

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

def Spec (row : Row R) : Prop :=
  row.e = row.e0 + row.e1 * 64

def main (row : Var Row F) : Circuit F Unit := do
  assertZero (decomposition row)

def circuit : FormalAssertion F Row where
  main
  Spec := Spec
  soundness := by
    circuit_proof_start [main, Spec, decomposition]
    exact left_eq_of_add_neg_eq_zero h_holds
  completeness := by
    circuit_proof_start [main, Spec, decomposition]
    rw [h_spec]
    ring

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

def Spec (row : Row R) : Prop :=
  IsBool row.g0 ∧
  row.g = row.g0 + row.g1 * 2 + row.g2 * 1024

def constraints (row : Row R) : Prop :=
  boolPoly row.g0 = 0 ∧ decomposition row = 0

def main (row : Var Row F) : Circuit F Unit := do
  assertZero (boolPoly row.g0)
  assertZero (decomposition row)

def circuit : FormalAssertion F Row where
  main
  Spec := Spec
  soundness := by
    circuit_proof_start [main, Spec, constraints, IsBool, boolPoly, decomposition]
    rcases h_holds with ⟨hg0, hdec⟩
    exact ⟨isBool_of_boolPoly_eq_zero (by simpa [boolPoly, sub_eq_add_neg] using hg0),
      left_eq_of_add_neg_eq_zero hdec⟩
  completeness := by
    circuit_proof_start [main, Spec, constraints, IsBool, boolPoly, decomposition]
    rcases h_spec with ⟨hg0, hdec⟩
    exact ⟨by simpa [boolPoly, sub_eq_add_neg] using boolPoly_eq_zero_of_isBool hg0,
      by rw [hdec]; ring⟩

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

def Spec (row : Row R) : Prop :=
  IsBool row.h1 ∧
  row.h = row.h0 + row.h1 * 32

def constraints (row : Row R) : Prop :=
  boolPoly row.h1 = 0 ∧ decomposition row = 0

def main (row : Var Row F) : Circuit F Unit := do
  assertZero (boolPoly row.h1)
  assertZero (decomposition row)

def circuit : FormalAssertion F Row where
  main
  Spec := Spec
  soundness := by
    circuit_proof_start [main, Spec, constraints, IsBool, boolPoly, decomposition]
    rcases h_holds with ⟨hh1, hdec⟩
    exact ⟨isBool_of_boolPoly_eq_zero (by simpa [boolPoly, sub_eq_add_neg] using hh1),
      left_eq_of_add_neg_eq_zero hdec⟩
  completeness := by
    circuit_proof_start [main, Spec, constraints, IsBool, boolPoly, decomposition]
    rcases h_spec with ⟨hh1, hdec⟩
    exact ⟨by simpa [boolPoly, sub_eq_add_neg] using boolPoly_eq_zero_of_isBool hh1,
      by rw [hdec]; ring⟩

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

def Spec (row : Row R) : Prop :=
  row.gdX = row.a + row.b0 * OfNat.ofNat (2 ^ 250) + row.b1 * OfNat.ofNat (2 ^ 254) ∧
    row.aPrime = row.a + OfNat.ofNat (2 ^ 130) - tP ∧
    (row.b1 = 0 ∨ row.b0 = 0) ∧
    (row.b1 = 0 ∨ row.z13A = 0) ∧
    (row.b1 = 0 ∨ row.z13APrime = 0)

def main (row : Var Row F) : Circuit F Unit := do
  assertZero (decomposition row)
  assertZero (aPrimeCheck row)
  assertZero (row.b1 * row.b0)
  assertZero (row.b1 * row.z13A)
  assertZero (row.b1 * row.z13APrime)

def circuit : FormalAssertion F Row where
  main
  Spec := Spec
  soundness := by
    circuit_proof_start [main, Spec, constraints, decomposition, aPrimeCheck, tP]
    rcases h_holds with ⟨hdec, hprime, hb0, hz13, hz13p⟩
    exact ⟨(left_eq_of_add_neg_eq_zero hdec).symm,
      by simpa [sub_eq_add_neg] using (left_eq_of_add_neg_eq_zero hprime).symm,
      mul_eq_zero.mp hb0, mul_eq_zero.mp hz13, mul_eq_zero.mp hz13p⟩
  completeness := by
    circuit_proof_start [main, Spec, constraints, decomposition, aPrimeCheck, tP]
    rcases h_spec with ⟨hdec, hprime, hb0, hz13, hz13p⟩
    constructor
    · rw [hdec]
      ring
    constructor
    · rw [hprime]
      ring
    exact ⟨mul_eq_zero_of_or hb0, mul_eq_zero_of_or hz13, mul_eq_zero_of_or hz13p⟩

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

def Spec (row : Row R) : Prop :=
  row.pkdX = row.b3 + row.c * 16 + row.d0 * OfNat.ofNat (2 ^ 254) ∧
    row.b3CPrime = row.b3 + row.c * 16 + OfNat.ofNat (2 ^ 140) - tP ∧
    (row.d0 = 0 ∨ row.z13C = 0) ∧
    (row.d0 = 0 ∨ row.z14B3CPrime = 0)

def main (row : Var Row F) : Circuit F Unit := do
  assertZero (decomposition row)
  assertZero (b3CPrimeCheck row)
  assertZero (row.d0 * row.z13C)
  assertZero (row.d0 * row.z14B3CPrime)

def circuit : FormalAssertion F Row where
  main
  Spec := Spec
  soundness := by
    circuit_proof_start [main, Spec, constraints, decomposition, b3CPrimeCheck, tP]
    rcases h_holds with ⟨hdec, hprime, hz13, hz14⟩
    exact ⟨(left_eq_of_add_neg_eq_zero hdec).symm,
      by simpa [sub_eq_add_neg] using (left_eq_of_add_neg_eq_zero hprime).symm,
      mul_eq_zero.mp hz13, mul_eq_zero.mp hz14⟩
  completeness := by
    circuit_proof_start [main, Spec, constraints, decomposition, b3CPrimeCheck, tP]
    rcases h_spec with ⟨hdec, hprime, hz13, hz14⟩
    constructor
    · rw [hdec]
      ring
    constructor
    · rw [hprime]
      ring
    exact ⟨mul_eq_zero_of_or hz13, mul_eq_zero_of_or hz14⟩

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

def Spec (row : Row R) : Prop :=
  row.value = row.d2 + row.d3 * 256 + row.e0 * 288230376151711744

def main (row : Var Row F) : Circuit F Unit := do
  assertZero (valueCheck row)

def circuit : FormalAssertion F Row where
  main
  Spec := Spec
  soundness := by
    circuit_proof_start [main, Spec, valueCheck]
    exact (left_eq_of_add_neg_eq_zero h_holds).symm
  completeness := by
    circuit_proof_start [main, Spec, valueCheck]
    rw [h_spec]
    ring

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

def Spec (row : Row R) : Prop :=
  row.rho = row.e1 + row.f * 16 + row.g0 * OfNat.ofNat (2 ^ 254) ∧
    row.e1FPrime = row.e1 + row.f * 16 + OfNat.ofNat (2 ^ 140) - tP ∧
    (row.g0 = 0 ∨ row.z13F = 0) ∧
    (row.g0 = 0 ∨ row.z14E1FPrime = 0)

def main (row : Var Row F) : Circuit F Unit := do
  assertZero (decomposition row)
  assertZero (e1FPrimeCheck row)
  assertZero (row.g0 * row.z13F)
  assertZero (row.g0 * row.z14E1FPrime)

def circuit : FormalAssertion F Row where
  main
  Spec := Spec
  soundness := by
    circuit_proof_start [main, Spec, constraints, decomposition, e1FPrimeCheck, tP]
    rcases h_holds with ⟨hdec, hprime, hz13, hz14⟩
    exact ⟨(left_eq_of_add_neg_eq_zero hdec).symm,
      by simpa [sub_eq_add_neg] using (left_eq_of_add_neg_eq_zero hprime).symm,
      mul_eq_zero.mp hz13, mul_eq_zero.mp hz14⟩
  completeness := by
    circuit_proof_start [main, Spec, constraints, decomposition, e1FPrimeCheck, tP]
    rcases h_spec with ⟨hdec, hprime, hz13, hz14⟩
    constructor
    · rw [hdec]
      ring
    constructor
    · rw [hprime]
      ring
    exact ⟨mul_eq_zero_of_or hz13, mul_eq_zero_of_or hz14⟩

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

def Spec (row : Row R) : Prop :=
  row.psi = row.g1 + row.g2 * 512 + row.h0 * OfNat.ofNat (2 ^ 249) +
    row.h1 * OfNat.ofNat (2 ^ 254) ∧
    row.g1G2Prime = row.g1 + row.g2 * 512 + OfNat.ofNat (2 ^ 130) - tP ∧
    (row.h1 = 0 ∨ row.h0 = 0) ∧
    (row.h1 = 0 ∨ row.z13G = 0) ∧
    (row.h1 = 0 ∨ row.z13G1G2Prime = 0)

def main (row : Var Row F) : Circuit F Unit := do
  assertZero (decomposition row)
  assertZero (g1G2PrimeCheck row)
  assertZero (row.h1 * row.h0)
  assertZero (row.h1 * row.z13G)
  assertZero (row.h1 * row.z13G1G2Prime)

def circuit : FormalAssertion F Row where
  main
  Spec := Spec
  soundness := by
    circuit_proof_start [main, Spec, constraints, decomposition, g1G2PrimeCheck, tP]
    rcases h_holds with ⟨hdec, hprime, hh0, hz13, hz13p⟩
    exact ⟨(left_eq_of_add_neg_eq_zero hdec).symm,
      by simpa [sub_eq_add_neg] using (left_eq_of_add_neg_eq_zero hprime).symm,
      mul_eq_zero.mp hh0, mul_eq_zero.mp hz13, mul_eq_zero.mp hz13p⟩
  completeness := by
    circuit_proof_start [main, Spec, constraints, decomposition, g1G2PrimeCheck, tP]
    rcases h_spec with ⟨hdec, hprime, hh0, hz13, hz13p⟩
    constructor
    · rw [hdec]
      ring
    constructor
    · rw [hprime]
      ring
    exact ⟨mul_eq_zero_of_or hh0, mul_eq_zero_of_or hz13, mul_eq_zero_of_or hz13p⟩

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

def Spec (row : Row R) : Prop :=
  IsBool row.k3 ∧
    row.j = row.lsb + row.k0 * 2 + row.z1J * 1024 ∧
    row.y = row.j + row.k2 * OfNat.ofNat (2 ^ 250) +
      row.k3 * OfNat.ofNat (2 ^ 254) ∧
    row.jPrime = row.j + OfNat.ofNat (2 ^ 130) - tP ∧
    (row.k3 = 0 ∨ row.k2 = 0) ∧
    (row.k3 = 0 ∨ row.z13J = 0) ∧
    (row.k3 = 0 ∨ row.z13JPrime = 0)

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
  Spec := Spec
  soundness := by
    circuit_proof_start [main, Spec, constraints, IsBool, boolPoly, jCheck, yCheck, jPrimeCheck, tP]
    rcases h_holds with ⟨hk3, hj, hy, hp, hk2, hz13, hz13p⟩
    exact ⟨isBool_of_boolPoly_eq_zero (by simpa [boolPoly, sub_eq_add_neg] using hk3),
      left_eq_of_add_neg_eq_zero hj, left_eq_of_add_neg_eq_zero hy,
      by simpa [sub_eq_add_neg] using (left_eq_of_add_neg_eq_zero hp).symm,
      mul_eq_zero.mp hk2, mul_eq_zero.mp hz13, mul_eq_zero.mp hz13p⟩
  completeness := by
    circuit_proof_start [main, Spec, constraints, IsBool, boolPoly, jCheck, yCheck, jPrimeCheck, tP]
    rcases h_spec with ⟨hk3, hj, hy, hp, hk2, hz13, hz13p⟩
    constructor
    · simpa [boolPoly, sub_eq_add_neg] using boolPoly_eq_zero_of_isBool hk3
    constructor
    · rw [hj]
      ring
    constructor
    · rw [hy]
      ring
    constructor
    · rw [hp]
      ring
    exact ⟨mul_eq_zero_of_or hk2, mul_eq_zero_of_or hz13, mul_eq_zero_of_or hz13p⟩

end YCanonicity

/-!
`note_commit` source-level wiring.

Reference:
`orchard@0.14.0/src/circuit/note_commit.rs`
- `gadgets::note_commit`

This assertion follows the values that the Rust gadget constructs:
the eight Sinsemilla message pieces `a` through `h`, the running-sum endpoints returned
by `CommitDomain::commit`, and the cells assigned into the decomposition and canonicity
custom gates above. The Sinsemilla commitment itself is represented by explicit
`computedCm*` row values; this file does not invent constraints for the commitment
algorithm beyond the separately ported Sinsemilla gates.
-/
namespace Wiring

variable [OfNat R 2] [OfNat R 4] [OfNat R 16] [OfNat R 32] [OfNat R 64]
  [OfNat R 256] [OfNat R 512] [OfNat R 1024]
  [OfNat R (2 ^ 130)] [OfNat R (2 ^ 140)] [OfNat R (2 ^ 249)]
  [OfNat R (2 ^ 250)] [OfNat R (2 ^ 254)] [OfNat R 288230376151711744]
  [OfNat R 45560315531419706090280762371685220353]

structure Row (F : Type) where
  b : DecomposeB.Row F
  d : DecomposeD.Row F
  e : DecomposeE.Row F
  g : DecomposeG.Row F
  h : DecomposeH.Row F
  gd : GdCanonicity.Row F
  pkd : PkdCanonicity.Row F
  value : ValueCanonicity.Row F
  rho : RhoCanonicity.Row F
  psi : PsiCanonicity.Row F
  gdY : YCanonicity.Row F
  pkdY : YCanonicity.Row F
  computedCmX : F
  computedCmY : F
  cmX : F
  cmY : F
deriving ProvableStruct

def b0Check (row : Row R) : R := row.b.b0 - row.gd.b0
def b1Check (row : Row R) : R := row.b.b1 - row.gd.b1
def b2Check (row : Row R) : R := row.b.b2 - row.gdY.lsb
def b3Check (row : Row R) : R := row.b.b3 - row.pkd.b3
def d0Check (row : Row R) : R := row.d.d0 - row.pkd.d0
def d1Check (row : Row R) : R := row.d.d1 - row.pkdY.lsb
def d2Check (row : Row R) : R := row.d.d2 - row.value.d2
def z1DCheck (row : Row R) : R := row.d.d3 - row.value.d3
def e0Check (row : Row R) : R := row.e.e0 - row.value.e0
def e1Check (row : Row R) : R := row.e.e1 - row.rho.e1
def g0Check (row : Row R) : R := row.g.g0 - row.rho.g0
def g1Check (row : Row R) : R := row.g.g1 - row.psi.g1
def z1GCheck (row : Row R) : R := row.g.g2 - row.psi.g2
def h0Check (row : Row R) : R := row.h.h0 - row.psi.h0
def h1Check (row : Row R) : R := row.h.h1 - row.psi.h1
def cmXCheck (row : Row R) : R := row.computedCmX - row.cmX
def cmYCheck (row : Row R) : R := row.computedCmY - row.cmY

def constraints (row : Row R) : Prop :=
  DecomposeB.constraints row.b ∧
    DecomposeD.constraints row.d ∧
    DecomposeE.decomposition row.e = 0 ∧
    DecomposeG.constraints row.g ∧
    DecomposeH.constraints row.h ∧
    GdCanonicity.constraints row.gd ∧
    PkdCanonicity.constraints row.pkd ∧
    ValueCanonicity.valueCheck row.value = 0 ∧
    RhoCanonicity.constraints row.rho ∧
    PsiCanonicity.constraints row.psi ∧
    YCanonicity.constraints row.gdY ∧
    YCanonicity.constraints row.pkdY ∧
    b0Check row = 0 ∧
    b1Check row = 0 ∧
    b2Check row = 0 ∧
    b3Check row = 0 ∧
    d0Check row = 0 ∧
    d1Check row = 0 ∧
    d2Check row = 0 ∧
    z1DCheck row = 0 ∧
    e0Check row = 0 ∧
    e1Check row = 0 ∧
    g0Check row = 0 ∧
    g1Check row = 0 ∧
    z1GCheck row = 0 ∧
    h0Check row = 0 ∧
    h1Check row = 0 ∧
    cmXCheck row = 0 ∧
    cmYCheck row = 0

def main (row : Var Row F) : Circuit F Unit := do
  assertZero (boolPoly row.b.b1)
  assertZero (boolPoly row.b.b2)
  assertZero (DecomposeB.decomposition row.b)
  assertZero (boolPoly row.d.d0)
  assertZero (boolPoly row.d.d1)
  assertZero (DecomposeD.decomposition row.d)
  assertZero (DecomposeE.decomposition row.e)
  assertZero (boolPoly row.g.g0)
  assertZero (DecomposeG.decomposition row.g)
  assertZero (boolPoly row.h.h1)
  assertZero (DecomposeH.decomposition row.h)
  assertZero (GdCanonicity.decomposition row.gd)
  assertZero (GdCanonicity.aPrimeCheck row.gd)
  assertZero (row.gd.b1 * row.gd.b0)
  assertZero (row.gd.b1 * row.gd.z13A)
  assertZero (row.gd.b1 * row.gd.z13APrime)
  assertZero (PkdCanonicity.decomposition row.pkd)
  assertZero (PkdCanonicity.b3CPrimeCheck row.pkd)
  assertZero (row.pkd.d0 * row.pkd.z13C)
  assertZero (row.pkd.d0 * row.pkd.z14B3CPrime)
  assertZero (ValueCanonicity.valueCheck row.value)
  assertZero (RhoCanonicity.decomposition row.rho)
  assertZero (RhoCanonicity.e1FPrimeCheck row.rho)
  assertZero (row.rho.g0 * row.rho.z13F)
  assertZero (row.rho.g0 * row.rho.z14E1FPrime)
  assertZero (PsiCanonicity.decomposition row.psi)
  assertZero (PsiCanonicity.g1G2PrimeCheck row.psi)
  assertZero (row.psi.h1 * row.psi.h0)
  assertZero (row.psi.h1 * row.psi.z13G)
  assertZero (row.psi.h1 * row.psi.z13G1G2Prime)
  assertZero (boolPoly row.gdY.k3)
  assertZero (YCanonicity.jCheck row.gdY)
  assertZero (YCanonicity.yCheck row.gdY)
  assertZero (YCanonicity.jPrimeCheck row.gdY)
  assertZero (row.gdY.k3 * row.gdY.k2)
  assertZero (row.gdY.k3 * row.gdY.z13J)
  assertZero (row.gdY.k3 * row.gdY.z13JPrime)
  assertZero (boolPoly row.pkdY.k3)
  assertZero (YCanonicity.jCheck row.pkdY)
  assertZero (YCanonicity.yCheck row.pkdY)
  assertZero (YCanonicity.jPrimeCheck row.pkdY)
  assertZero (row.pkdY.k3 * row.pkdY.k2)
  assertZero (row.pkdY.k3 * row.pkdY.z13J)
  assertZero (row.pkdY.k3 * row.pkdY.z13JPrime)
  assertZero (b0Check row)
  assertZero (b1Check row)
  assertZero (b2Check row)
  assertZero (b3Check row)
  assertZero (d0Check row)
  assertZero (d1Check row)
  assertZero (d2Check row)
  assertZero (z1DCheck row)
  assertZero (e0Check row)
  assertZero (e1Check row)
  assertZero (g0Check row)
  assertZero (g1Check row)
  assertZero (z1GCheck row)
  assertZero (h0Check row)
  assertZero (h1Check row)
  assertZero (cmXCheck row)
  assertZero (cmYCheck row)

def circuit : FormalAssertion F Row where
  main
  Spec := constraints
  soundness := by
    circuit_proof_start [main, constraints, b0Check, b1Check, b2Check, b3Check,
      d0Check, d1Check, d2Check, z1DCheck, e0Check, e1Check, g0Check, g1Check,
      z1GCheck, h0Check, h1Check, cmXCheck, cmYCheck, DecomposeB.constraints,
      DecomposeB.decomposition, DecomposeD.constraints, DecomposeD.decomposition,
      DecomposeE.decomposition, DecomposeG.constraints, DecomposeG.decomposition,
      DecomposeH.constraints, DecomposeH.decomposition, GdCanonicity.constraints,
      GdCanonicity.decomposition, GdCanonicity.aPrimeCheck,
      PkdCanonicity.constraints, PkdCanonicity.decomposition,
      PkdCanonicity.b3CPrimeCheck, ValueCanonicity.valueCheck,
      RhoCanonicity.constraints, RhoCanonicity.decomposition,
      RhoCanonicity.e1FPrimeCheck, PsiCanonicity.constraints,
      PsiCanonicity.decomposition, PsiCanonicity.g1G2PrimeCheck,
      YCanonicity.constraints, YCanonicity.jCheck, YCanonicity.yCheck,
      YCanonicity.jPrimeCheck, boolPoly, tP]
    simp_all [sub_eq_add_neg]
  completeness := by
    circuit_proof_start [main, constraints, b0Check, b1Check, b2Check, b3Check,
      d0Check, d1Check, d2Check, z1DCheck, e0Check, e1Check, g0Check, g1Check,
      z1GCheck, h0Check, h1Check, cmXCheck, cmYCheck, DecomposeB.constraints,
      DecomposeB.decomposition, DecomposeD.constraints, DecomposeD.decomposition,
      DecomposeE.decomposition, DecomposeG.constraints, DecomposeG.decomposition,
      DecomposeH.constraints, DecomposeH.decomposition, GdCanonicity.constraints,
      GdCanonicity.decomposition, GdCanonicity.aPrimeCheck,
      PkdCanonicity.constraints, PkdCanonicity.decomposition,
      PkdCanonicity.b3CPrimeCheck, ValueCanonicity.valueCheck,
      RhoCanonicity.constraints, RhoCanonicity.decomposition,
      RhoCanonicity.e1FPrimeCheck, PsiCanonicity.constraints,
      PsiCanonicity.decomposition, PsiCanonicity.g1G2PrimeCheck,
      YCanonicity.constraints, YCanonicity.jCheck, YCanonicity.yCheck,
      YCanonicity.jPrimeCheck, boolPoly, tP]
    simp_all [sub_eq_add_neg]

end Wiring

/-!
Note-commitment output connected to Sinsemilla commitment arithmetic.

Reference:
`orchard@0.14.0/src/circuit/note_commit.rs`
- `gadgets::note_commit`

`gadgets::note_commit` builds the message/decomposition rows, calls
`CommitDomain::commit`, and uses the returned point as the computed note commitment.
`Wiring.circuit` records the message-piece and canonicity wiring. This assertion connects
its explicit `computedCm*` outputs to the `Sinsemilla.Commit.circuit` output point.
-/
namespace WiringWithCommit

variable [OfNat R 2] [OfNat R 3]

structure Row (F : Type) where
  note : Wiring.Row F
  commit : Sinsemilla.Commit.Row F
deriving ProvableStruct

def cmXCheck (row : Row R) : R :=
  row.commit.commitmentX - row.note.computedCmX

def cmYCheck (row : Row R) : R :=
  row.commit.commitmentY - row.note.computedCmY

def constraints (row : Row R) : Prop :=
  Sinsemilla.Commit.constraints row.commit ∧
    cmXCheck row = 0 ∧
    cmYCheck row = 0

def main (row : Var Row F) : Circuit F Unit := do
  Sinsemilla.Commit.circuit row.commit
  assertZero (cmXCheck row)
  assertZero (cmYCheck row)

def circuit : FormalAssertion F Row where
  main
  Spec := constraints
  soundness := by
    circuit_proof_start [main, constraints, cmXCheck, cmYCheck,
      Sinsemilla.Commit.circuit, Sinsemilla.Commit.constraints, Sinsemilla.Commit.addRow,
      Ecc.CompleteAdd.circuit, Ecc.CompleteAdd.constraints, Ecc.CompleteAdd.poly1,
      Ecc.CompleteAdd.poly2, Ecc.CompleteAdd.poly3a, Ecc.CompleteAdd.poly3b,
      Ecc.CompleteAdd.poly3c, Ecc.CompleteAdd.poly3d, Ecc.CompleteAdd.poly4a,
      Ecc.CompleteAdd.poly4b, Ecc.CompleteAdd.poly5a, Ecc.CompleteAdd.poly5b,
      Ecc.CompleteAdd.poly6a, Ecc.CompleteAdd.poly6b, Ecc.CompleteAdd.nonexceptionalXR,
      Ecc.CompleteAdd.nonexceptionalYR, Ecc.CompleteAdd.ifAlpha,
      Ecc.CompleteAdd.ifBeta, Ecc.CompleteAdd.ifGamma, Ecc.CompleteAdd.ifDelta,
      Ecc.CompleteAdd.xQMinusXP, Ecc.CompleteAdd.xPMinusXR, Ecc.CompleteAdd.yQPlusYP]
    simp_all [sub_eq_add_neg]
  completeness := by
    circuit_proof_start [main, constraints, cmXCheck, cmYCheck,
      Sinsemilla.Commit.circuit, Sinsemilla.Commit.constraints, Sinsemilla.Commit.addRow,
      Ecc.CompleteAdd.circuit, Ecc.CompleteAdd.constraints, Ecc.CompleteAdd.poly1,
      Ecc.CompleteAdd.poly2, Ecc.CompleteAdd.poly3a, Ecc.CompleteAdd.poly3b,
      Ecc.CompleteAdd.poly3c, Ecc.CompleteAdd.poly3d, Ecc.CompleteAdd.poly4a,
      Ecc.CompleteAdd.poly4b, Ecc.CompleteAdd.poly5a, Ecc.CompleteAdd.poly5b,
      Ecc.CompleteAdd.poly6a, Ecc.CompleteAdd.poly6b, Ecc.CompleteAdd.nonexceptionalXR,
      Ecc.CompleteAdd.nonexceptionalYR, Ecc.CompleteAdd.ifAlpha,
      Ecc.CompleteAdd.ifBeta, Ecc.CompleteAdd.ifGamma, Ecc.CompleteAdd.ifDelta,
      Ecc.CompleteAdd.xQMinusXP, Ecc.CompleteAdd.xPMinusXR, Ecc.CompleteAdd.yQPlusYP]
    simp_all [sub_eq_add_neg]

end WiringWithCommit

end NoteCommit
end Orchard
