import Clean.Circuit
import Clean.Gadgets.Boolean
import Clean.Orchard.Ecc
import Clean.Utils.Tactics
import Clean.Utils.Tactics.ProvableStructDeriving

/-!
# Orchard note commitment gates

Clean ports of Orchard `NoteCommit` arithmetic gates.

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

Most assertions model the enabled Halo2 custom-gate polynomials, not selector, rotation,
column-layout, lookup, or assignment machinery.

The synthesis-level `gadgets::note_commit` entry circuit lives in `Clean.Orchard.NoteCommit`,
because it depends on `Sinsemilla.Domain` while this low-level gate module is imported by
scalar-multiplication definitions.
-/

namespace Orchard.NoteCommit

variable {F : Type} [Field F]

private theorem mul_eq_zero_of_or {a b : F} (h : a = 0 ∨ b = 0) : a * b = 0 := by
  rcases h with h | h <;> rw [h] <;> simp

private theorem left_eq_of_add_neg_eq_zero {a b : F} (h : a + -b = 0) : a = b :=
  sub_eq_zero.mp (by simpa [sub_eq_add_neg] using h)

namespace Gate

namespace DecomposeB

structure Row (F : Type) where
  b : F
  b0 : F
  b1 : F
  b2 : F
  b3 : F
deriving ProvableStruct

def Spec (row : Row Ecc.Fp) : Prop :=
  IsBool row.b1 ∧
  IsBool row.b2 ∧
  row.b = row.b0 + row.b1 * 16 + row.b2 * 32 + row.b3 * 64

def main (row : Var Row Ecc.Fp) : Circuit Ecc.Fp Unit := do
  assertBool row.b1
  assertBool row.b2
  assertZero (row.b - (row.b0 + row.b1 * 16 + row.b2 * 32 + row.b3 * 64))

def circuit : FormalAssertion Ecc.Fp Row where
  name := "GATE NoteCommit MessagePiece b"
  main
  Spec := Spec
  soundness := by
    circuit_proof_start
    rcases h_holds with ⟨hb1, hb2, hdec⟩
    exact ⟨hb1, hb2, left_eq_of_add_neg_eq_zero hdec⟩
  completeness := by
    circuit_proof_start
    rcases h_spec with ⟨hb1, hb2, hdec⟩
    exact ⟨hb1, hb2, by rw [hdec]; ring⟩

end DecomposeB

namespace DecomposeD

structure Row (F : Type) where
  d : F
  d0 : F
  d1 : F
  d2 : F
  d3 : F
deriving ProvableStruct

def Spec (row : Row Ecc.Fp) : Prop :=
  IsBool row.d0 ∧
  IsBool row.d1 ∧
  row.d = row.d0 + row.d1 * 2 + row.d2 * 4 + row.d3 * 1024

def main (row : Var Row Ecc.Fp) : Circuit Ecc.Fp Unit := do
  assertBool row.d0
  assertBool row.d1
  assertZero (row.d - (row.d0 + row.d1 * 2 + row.d2 * 4 + row.d3 * 1024))

def circuit : FormalAssertion Ecc.Fp Row where
  name := "GATE NoteCommit MessagePiece d"
  main
  Spec := Spec
  soundness := by
    circuit_proof_start
    rcases h_holds with ⟨hd0, hd1, hdec⟩
    exact ⟨hd0, hd1, left_eq_of_add_neg_eq_zero hdec⟩
  completeness := by
    circuit_proof_start
    rcases h_spec with ⟨hd0, hd1, hdec⟩
    exact ⟨hd0, hd1, by rw [hdec]; ring⟩

end DecomposeD

namespace DecomposeE

structure Row (F : Type) where
  e : F
  e0 : F
  e1 : F
deriving ProvableStruct

def Spec (row : Row Ecc.Fp) : Prop :=
  row.e = row.e0 + row.e1 * 64

def main (row : Var Row Ecc.Fp) : Circuit Ecc.Fp Unit := do
  assertZero (row.e - (row.e0 + row.e1 * 64))

def circuit : FormalAssertion Ecc.Fp Row where
  name := "GATE NoteCommit MessagePiece e"
  main
  Spec := Spec
  soundness := by
    circuit_proof_start
    exact left_eq_of_add_neg_eq_zero h_holds
  completeness := by
    circuit_proof_start
    rw [h_spec]
    ring

end DecomposeE

namespace DecomposeG

structure Row (F : Type) where
  g : F
  g0 : F
  g1 : F
  g2 : F
deriving ProvableStruct

def Spec (row : Row Ecc.Fp) : Prop :=
  IsBool row.g0 ∧
  row.g = row.g0 + row.g1 * 2 + row.g2 * 1024

def main (row : Var Row Ecc.Fp) : Circuit Ecc.Fp Unit := do
  assertBool row.g0
  assertZero (row.g - (row.g0 + row.g1 * 2 + row.g2 * 1024))

def circuit : FormalAssertion Ecc.Fp Row where
  name := "GATE NoteCommit MessagePiece g"
  main
  Spec := Spec
  soundness := by
    circuit_proof_start
    rcases h_holds with ⟨hg0, hdec⟩
    exact ⟨hg0, left_eq_of_add_neg_eq_zero hdec⟩
  completeness := by
    circuit_proof_start
    rcases h_spec with ⟨hg0, hdec⟩
    exact ⟨hg0, by rw [hdec]; ring⟩

end DecomposeG

namespace DecomposeH

structure Row (F : Type) where
  h : F
  h0 : F
  h1 : F
deriving ProvableStruct

def Spec (row : Row Ecc.Fp) : Prop :=
  IsBool row.h1 ∧
  row.h = row.h0 + row.h1 * 32

def main (row : Var Row Ecc.Fp) : Circuit Ecc.Fp Unit := do
  assertBool row.h1
  assertZero (row.h - (row.h0 + row.h1 * 32))

def circuit : FormalAssertion Ecc.Fp Row where
  name := "GATE NoteCommit MessagePiece h"
  main
  Spec := Spec
  soundness := by
    circuit_proof_start
    rcases h_holds with ⟨hh1, hdec⟩
    exact ⟨hh1, left_eq_of_add_neg_eq_zero hdec⟩
  completeness := by
    circuit_proof_start
    rcases h_spec with ⟨hh1, hdec⟩
    exact ⟨hh1, by rw [hdec]; ring⟩

end DecomposeH

namespace GdCanonicity

structure Row (F : Type) where
  gdX : F
  b0 : F
  b1 : F
  a : F
  aPrime : F
  z13A : F
  z13APrime : F
deriving ProvableStruct

def Spec (row : Row Ecc.Fp) : Prop :=
  row.gdX = row.a + row.b0 * OfNat.ofNat (2 ^ 250) + row.b1 * OfNat.ofNat (2 ^ 254) ∧
    row.aPrime = row.a + OfNat.ofNat (2 ^ 130) - Ecc.tP ∧
    (row.b1 = 0 ∨ row.b0 = 0) ∧
    (row.b1 = 0 ∨ row.z13A = 0) ∧
    (row.b1 = 0 ∨ row.z13APrime = 0)

def main (row : Var Row Ecc.Fp) : Circuit Ecc.Fp Unit := do
  assertZero (row.a + row.b0 * OfNat.ofNat (2 ^ 250) +
    row.b1 * OfNat.ofNat (2 ^ 254) - row.gdX)
  assertZero (row.a + Expression.const ((2 ^ 130 : ℕ) : Ecc.Fp) -
    Expression.const Ecc.tP - row.aPrime)
  assertZero (row.b1 * row.b0)
  assertZero (row.b1 * row.z13A)
  assertZero (row.b1 * row.z13APrime)

def circuit : FormalAssertion Ecc.Fp Row where
  name := "GATE NoteCommit input g_d"
  main
  Spec := Spec
  soundness := by
    circuit_proof_start [Ecc.tP]
    rcases h_holds with ⟨hdec, hprime, hb0, hz13, hz13p⟩
    exact ⟨(left_eq_of_add_neg_eq_zero hdec).symm,
      by simpa [sub_eq_add_neg] using (left_eq_of_add_neg_eq_zero hprime).symm,
      mul_eq_zero.mp hb0, mul_eq_zero.mp hz13, mul_eq_zero.mp hz13p⟩
  completeness := by
    circuit_proof_start [Ecc.tP]
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

structure Row (F : Type) where
  pkdX : F
  b3 : F
  d0 : F
  c : F
  b3CPrime : F
  z13C : F
  z14B3CPrime : F
deriving ProvableStruct

def Spec (row : Row Ecc.Fp) : Prop :=
  row.pkdX = row.b3 + row.c * 16 + row.d0 * OfNat.ofNat (2 ^ 254) ∧
    row.b3CPrime = row.b3 + row.c * 16 + OfNat.ofNat (2 ^ 140) - Ecc.tP ∧
    (row.d0 = 0 ∨ row.z13C = 0) ∧
    (row.d0 = 0 ∨ row.z14B3CPrime = 0)

def main (row : Var Row Ecc.Fp) : Circuit Ecc.Fp Unit := do
  assertZero (row.b3 + row.c * 16 + row.d0 * OfNat.ofNat (2 ^ 254) - row.pkdX)
  assertZero (row.b3 + row.c * 16 + Expression.const ((2 ^ 140 : ℕ) : Ecc.Fp) -
    Expression.const Ecc.tP - row.b3CPrime)
  assertZero (row.d0 * row.z13C)
  assertZero (row.d0 * row.z14B3CPrime)

def circuit : FormalAssertion Ecc.Fp Row where
  name := "GATE NoteCommit input pk_d"
  main
  Spec := Spec
  soundness := by
    circuit_proof_start [Ecc.tP]
    rcases h_holds with ⟨hdec, hprime, hz13, hz14⟩
    exact ⟨(left_eq_of_add_neg_eq_zero hdec).symm,
      by simpa [sub_eq_add_neg] using (left_eq_of_add_neg_eq_zero hprime).symm,
      mul_eq_zero.mp hz13, mul_eq_zero.mp hz14⟩
  completeness := by
    circuit_proof_start [Ecc.tP]
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

structure Row (F : Type) where
  value : F
  d2 : F
  d3 : F
  e0 : F
deriving ProvableStruct

def Spec (row : Row Ecc.Fp) : Prop :=
  row.value = row.d2 + row.d3 * 256 + row.e0 * 288230376151711744

def main (row : Var Row Ecc.Fp) : Circuit Ecc.Fp Unit := do
  assertZero (row.d2 + row.d3 * 256 + row.e0 * 288230376151711744 - row.value)

def circuit : FormalAssertion Ecc.Fp Row where
  name := "GATE NoteCommit input value"
  main
  Spec := Spec
  soundness := by
    circuit_proof_start
    exact (left_eq_of_add_neg_eq_zero h_holds).symm
  completeness := by
    circuit_proof_start
    rw [h_spec]
    ring

end ValueCanonicity

namespace RhoCanonicity

structure Row (F : Type) where
  rho : F
  e1 : F
  g0 : F
  f : F
  e1FPrime : F
  z13F : F
  z14E1FPrime : F
deriving ProvableStruct

def Spec (row : Row Ecc.Fp) : Prop :=
  row.rho = row.e1 + row.f * 16 + row.g0 * OfNat.ofNat (2 ^ 254) ∧
    row.e1FPrime = row.e1 + row.f * 16 + OfNat.ofNat (2 ^ 140) - Ecc.tP ∧
    (row.g0 = 0 ∨ row.z13F = 0) ∧
    (row.g0 = 0 ∨ row.z14E1FPrime = 0)

def main (row : Var Row Ecc.Fp) : Circuit Ecc.Fp Unit := do
  assertZero (row.e1 + row.f * 16 + row.g0 * OfNat.ofNat (2 ^ 254) - row.rho)
  assertZero (row.e1 + row.f * 16 + Expression.const ((2 ^ 140 : ℕ) : Ecc.Fp) -
    Expression.const Ecc.tP - row.e1FPrime)
  assertZero (row.g0 * row.z13F)
  assertZero (row.g0 * row.z14E1FPrime)

def circuit : FormalAssertion Ecc.Fp Row where
  name := "GATE NoteCommit input rho"
  main
  Spec := Spec
  soundness := by
    circuit_proof_start [Ecc.tP]
    rcases h_holds with ⟨hdec, hprime, hz13, hz14⟩
    exact ⟨(left_eq_of_add_neg_eq_zero hdec).symm,
      by simpa [sub_eq_add_neg] using (left_eq_of_add_neg_eq_zero hprime).symm,
      mul_eq_zero.mp hz13, mul_eq_zero.mp hz14⟩
  completeness := by
    circuit_proof_start [Ecc.tP]
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

def Spec (row : Row Ecc.Fp) : Prop :=
  row.psi = row.g1 + row.g2 * 512 + row.h0 * OfNat.ofNat (2 ^ 249) +
    row.h1 * OfNat.ofNat (2 ^ 254) ∧
    row.g1G2Prime = row.g1 + row.g2 * 512 + OfNat.ofNat (2 ^ 130) - Ecc.tP ∧
    (row.h1 = 0 ∨ row.h0 = 0) ∧
    (row.h1 = 0 ∨ row.z13G = 0) ∧
    (row.h1 = 0 ∨ row.z13G1G2Prime = 0)

def main (row : Var Row Ecc.Fp) : Circuit Ecc.Fp Unit := do
  assertZero (row.g1 + row.g2 * 512 + row.h0 * OfNat.ofNat (2 ^ 249) +
    row.h1 * OfNat.ofNat (2 ^ 254) - row.psi)
  assertZero (row.g1 + row.g2 * 512 + Expression.const ((2 ^ 130 : ℕ) : Ecc.Fp) -
    Expression.const Ecc.tP - row.g1G2Prime)
  assertZero (row.h1 * row.h0)
  assertZero (row.h1 * row.z13G)
  assertZero (row.h1 * row.z13G1G2Prime)

def circuit : FormalAssertion Ecc.Fp Row where
  name := "GATE NoteCommit input psi"
  main
  Spec := Spec
  soundness := by
    circuit_proof_start [Ecc.tP]
    rcases h_holds with ⟨hdec, hprime, hh0, hz13, hz13p⟩
    exact ⟨(left_eq_of_add_neg_eq_zero hdec).symm,
      by simpa [sub_eq_add_neg] using (left_eq_of_add_neg_eq_zero hprime).symm,
      mul_eq_zero.mp hh0, mul_eq_zero.mp hz13, mul_eq_zero.mp hz13p⟩
  completeness := by
    circuit_proof_start [Ecc.tP]
    rcases h_spec with ⟨hdec, hprime, hh0, hz13, hz13p⟩
    constructor
    · rw [hdec]
      ring
    constructor
    · rw [hprime]
      ring
    exact ⟨mul_eq_zero_of_or hh0, mul_eq_zero_of_or hz13, mul_eq_zero_of_or hz13p⟩

end PsiCanonicity

end Gate

namespace YCanonicity.Gate

structure Row (F : Type) where
  y : F
  lsb : F
  k0 : F
  k2 : F
  k3 : F
  j : F
  z1J : F
  z13J : F
  j' : F
  z13J' : F
deriving ProvableStruct

def Spec (row : Row Ecc.Fp) : Prop :=
  IsBool row.k3 ∧
    row.j = row.lsb + row.k0 * 2 + row.z1J * 1024 ∧
    row.y = row.j + row.k2 * ((2 ^ 250 : ℕ) : Ecc.Fp) +
      row.k3 * ((2 ^ 254 : ℕ) : Ecc.Fp) ∧
    row.j' = row.j + ((2 ^ 130 : ℕ) : Ecc.Fp) - Ecc.tP ∧
    (row.k3 = 0 ∨ row.k2 = 0) ∧
    (row.k3 = 0 ∨ row.z13J = 0) ∧
    (row.k3 = 0 ∨ row.z13J' = 0)

def main (row : Var Row Ecc.Fp) : Circuit Ecc.Fp Unit := do
  assertBool row.k3
  assertZero (row.j - (row.lsb + row.k0 * 2 + row.z1J * 1024))
  assertZero (row.y - (row.j + row.k2 * ((2 ^ 250 : ℕ) : Ecc.Fp) +
    row.k3 * ((2 ^ 254 : ℕ) : Ecc.Fp)))
  assertZero (row.j + Expression.const ((2 ^ 130 : ℕ) : Ecc.Fp) -
    Expression.const Ecc.tP - row.j')
  assertZero (row.k3 * row.k2)
  assertZero (row.k3 * row.z13J)
  assertZero (row.k3 * row.z13J')

def circuit : FormalAssertion Ecc.Fp Row where
  name := "GATE y coordinate checks"
  main
  Spec := Spec
  soundness := by
    circuit_proof_start [Ecc.tP]
    rcases h_holds with ⟨hk3, hj, hy, hp, hk2, hz13, hz13p⟩
    exact ⟨hk3, left_eq_of_add_neg_eq_zero hj, left_eq_of_add_neg_eq_zero hy,
      by simpa [sub_eq_add_neg] using (left_eq_of_add_neg_eq_zero hp).symm,
      mul_eq_zero.mp hk2, mul_eq_zero.mp hz13, mul_eq_zero.mp hz13p⟩
  completeness := by
    circuit_proof_start [Ecc.tP]
    rcases h_spec with ⟨hk3, hj, hy, hp, hk2, hz13, hz13p⟩
    constructor
    · exact hk3
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

end YCanonicity.Gate

end Orchard.NoteCommit
