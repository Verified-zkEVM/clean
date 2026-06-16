import Clean.Circuit
import Clean.Gadgets.Boolean
import Clean.Orchard.Ecc
import Clean.Orchard.Specs.Bitrange
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

/-! ### Foundational bit-decomposition / canonicity facts

These are stated over `Orchard.Specs.bitrange` and the Pallas base modulus, with no
reference to any particular circuit cell (`y`, `j`, …). The canonicity gates build on
them. -/

open CompElliptic.Fields.Pasta (PALLAS_BASE_CARD)
open Orchard.Specs (bitrange bitrange_lt bitrange_add)

/-- `t_P`, the Pallas base modulus minus `2^254`, as a natural number. -/
def tPNat : ℕ := 45560315531419706090280762371685220353

/-- The defining split of the Pallas base modulus: `p = 2^254 + t_P`. -/
theorem pallasBaseCard_eq : PALLAS_BASE_CARD = 2 ^ 254 + tPNat := by
  norm_num [PALLAS_BASE_CARD, tPNat]

/-- A `< 2^255` value is the sum of its low 250 bits, next 4 bits, and top bit. -/
theorem bit_decomp_255 {n : ℕ} (hn : n < 2 ^ 255) :
    n = bitrange n 0 250 + 2 ^ 250 * bitrange n 250 4 + 2 ^ 254 * bitrange n 254 1 := by
  simp only [bitrange, pow_zero, Nat.div_one]
  omega

/-- Canonicity with the top bit set: for `n < p` with bit 254 set, bits 250–253 vanish
and the low 250 bits lie below `t_P` (hence the `+2^130-t_P` shift stays below `2^130`). -/
theorem high_bit_canonical {n : ℕ} (hn : n < PALLAS_BASE_CARD) (hhigh : bitrange n 254 1 = 1) :
    bitrange n 250 4 = 0 ∧ bitrange n 0 250 < tPNat ∧
      bitrange n 0 250 + 2 ^ 130 - tPNat < 2 ^ 130 := by
  have hdec := bit_decomp_255 (lt_trans hn (by norm_num [PALLAS_BASE_CARD]))
  have hlo := bitrange_lt n 0 250
  have hk2 := bitrange_lt n 250 4
  rw [hhigh] at hdec
  rw [pallasBaseCard_eq] at hn
  norm_num [tPNat] at hlo hk2 hn hdec ⊢
  omega

/-- `lsb` is the low (sign) bit of the field element `y`. -/
def IsLowBit (y lsb : Ecc.Fp) : Prop :=
  lsb = ((if y.val.testBit 0 then 1 else 0 : ℕ) : Ecc.Fp)

theorem nat_mod_two_isBool (n : ℕ) : IsBool (((n % 2 : ℕ) : Ecc.Fp)) := by
  have hlt : n % 2 < 2 := Nat.mod_lt _ (by norm_num)
  interval_cases n % 2 <;> simp [IsBool]

theorem isLowBit_iff_mod_two {y lsb : Ecc.Fp} :
    IsLowBit y lsb ↔ lsb = ((y.val % 2 : ℕ) : Ecc.Fp) := by
  have key : (if y.val.testBit 0 then (1 : ℕ) else 0) = y.val % 2 := by
    rw [Nat.testBit_zero]
    rcases Nat.mod_two_eq_zero_or_one y.val with hm | hm <;> simp [hm]
  rw [IsLowBit, key]

/-- `Ecc.tP` as the cast of the natural number `tPNat`. -/
theorem tP_eq : Ecc.tP = ((tPNat : ℕ) : Ecc.Fp) := by
  rw [Ecc.tP, tPNat]; norm_num

/-- A 1-bit field slice is Boolean. -/
theorem bitrange_one_isBool (n start : ℕ) :
    IsBool ((bitrange n start 1 : ℕ) : Ecc.Fp) := by
  have h : bitrange n start 1 < 2 := by simpa using bitrange_lt n start 1
  interval_cases (bitrange n start 1) <;> simp [IsBool]

/-- The low 250-bit field splits into the sign bit, the next 9 bits, and the rest. -/
theorem low_250_decomp (n : ℕ) :
    bitrange n 0 250 = bitrange n 0 1 + 2 * bitrange n 1 9 + 1024 * bitrange n 10 240 := by
  have h1 := bitrange_add n 0 1 249
  have h2 := bitrange_add n 1 9 240
  norm_num at h1 h2
  rw [h1, h2]; ring

/-- With the top bit set, the bits 130–249 of a canonical value vanish. -/
theorem high_bit_z13_zero {n : ℕ} (hn : n < PALLAS_BASE_CARD)
    (hhigh : bitrange n 254 1 = 1) : bitrange n 130 120 = 0 := by
  obtain ⟨_, hlo, _⟩ := high_bit_canonical hn hhigh
  have hsplit := bitrange_add n 0 130 120
  have htp : tPNat < 2 ^ 130 := by norm_num [tPNat]
  have key : bitrange n 0 (130 + 120) < 2 ^ 130 := by
    rw [show (130 : ℕ) + 120 = 250 by norm_num]; omega
  rw [hsplit] at key
  rcases Nat.eq_zero_or_pos (bitrange n (0 + 130) 120) with h | h
  · simpa using h
  · exfalso
    have hge : 2 ^ 130 ≤ 2 ^ 130 * bitrange n (0 + 130) 120 := Nat.le_mul_of_pos_right _ h
    omega

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

/-- The gate runs inside `y_canonicity`, where the surrounding running-sum lookups force
each supporting cell to be the corresponding bit slice of `y`. Those semantics are the
gate's rely-conditions: every cell equals its `bitrange` of `y.val` (with `j'` the
canonicity-shifted low part). The sign bit `lsb` is *not* assumed — the gate's constraints
pin it down, which is exactly what `Spec` records. -/
def Assumptions (row : Row Ecc.Fp) : Prop :=
  row.k0 = ((bitrange row.y.val 1 9 : ℕ) : Ecc.Fp) ∧
    row.k2 = ((bitrange row.y.val 250 4 : ℕ) : Ecc.Fp) ∧
    row.k3 = ((bitrange row.y.val 254 1 : ℕ) : Ecc.Fp) ∧
    row.j = ((bitrange row.y.val 0 250 : ℕ) : Ecc.Fp) ∧
    row.z1J = ((bitrange row.y.val 10 240 : ℕ) : Ecc.Fp) ∧
    row.z13J = ((bitrange row.y.val 130 120 : ℕ) : Ecc.Fp) ∧
    row.j'.val = bitrange row.y.val 0 250 + 2 ^ 130 - tPNat ∧
    row.z13J' = ((row.j'.val / 2 ^ 130 : ℕ) : Ecc.Fp)

/-- The gate's payoff: `lsb` is the low (sign) bit of the `y` coordinate. -/
def Spec (row : Row Ecc.Fp) : Prop :=
  IsLowBit row.y row.lsb

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
  Assumptions := Assumptions
  Spec := Spec
  soundness := by
    circuit_proof_start
    obtain ⟨hk0, _, _, hj, hz1J, _, _, _⟩ := h_assumptions
    obtain ⟨_, hj_eq, _⟩ := h_holds
    -- `hj_eq` says the witnessed `j` equals `lsb + 2·k0 + 1024·z1J`; substituting the
    -- bit-slice values of `j`, `k0`, `z1J` isolates `lsb` as the low bit of `y`.
    rw [isLowBit_iff_mod_two,
      show input_y.val % 2 = bitrange input_y.val 0 1 from by simp [bitrange]]
    have hcast : ((bitrange input_y.val 0 250 : ℕ) : Ecc.Fp)
        = ((bitrange input_y.val 0 1 : ℕ) : Ecc.Fp)
          + 2 * ((bitrange input_y.val 1 9 : ℕ) : Ecc.Fp)
          + 1024 * ((bitrange input_y.val 10 240 : ℕ) : Ecc.Fp) := by
      rw [low_250_decomp]; push_cast; ring
    rw [hj, hk0, hz1J, hcast] at hj_eq
    linear_combination -hj_eq
  completeness := by
    circuit_proof_start
    obtain ⟨hk0, hk2, hk3, hj, hz1J, hz13, hj', hz13'⟩ := h_assumptions
    have hyval : input_y.val < PALLAS_BASE_CARD := ZMod.val_lt input_y
    have hyval255 : input_y.val < 2 ^ 255 := lt_trans hyval (by norm_num [PALLAS_BASE_CARD])
    -- `lsb` is the low bit of `y`, supplied by the `Spec`.
    have hlsb : input_lsb = ((bitrange input_y.val 0 1 : ℕ) : Ecc.Fp) := by
      rw [isLowBit_iff_mod_two] at h_spec
      rw [h_spec, show input_y.val % 2 = bitrange input_y.val 0 1 from by simp [bitrange]]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- k3 Boolean
      rw [hk3]; exact bitrange_one_isBool _ _
    · -- j = lsb + 2·k0 + 1024·z1J
      rw [hj, hk0, hz1J, hlsb, low_250_decomp input_y.val]; push_cast; ring
    · -- y = j + k2·2^250 + k3·2^254
      -- `bit_decomp_255` reconstructs `y` from its slices; cast it and recombine with the
      -- cell equalities.  (Rewriting `input_y` directly would also hit the `input_y.val`
      -- buried inside each `bitrange`, so we feed everything to `linear_combination`.)
      have hyv : input_y = ((input_y.val : ℕ) : Ecc.Fp) :=
        (ZMod.natCast_rightInverse input_y).symm
      have hdcast : ((input_y.val : ℕ) : Ecc.Fp)
          = ((bitrange input_y.val 0 250 : ℕ) : Ecc.Fp)
            + ((bitrange input_y.val 250 4 : ℕ) : Ecc.Fp) * ((2 ^ 250 : ℕ) : Ecc.Fp)
            + ((bitrange input_y.val 254 1 : ℕ) : Ecc.Fp) * ((2 ^ 254 : ℕ) : Ecc.Fp) := by
        conv_lhs => rw [bit_decomp_255 hyval255]
        push_cast; ring
      linear_combination hyv + hdcast - hj - ((2 ^ 250 : ℕ) : Ecc.Fp) * hk2
        - ((2 ^ 254 : ℕ) : Ecc.Fp) * hk3
    · -- j' = j + 2^130 - t_P
      have htp : tPNat ≤ bitrange input_y.val 0 250 + 2 ^ 130 := by
        have h1 : tPNat < 2 ^ 130 := by norm_num [tPNat]
        omega
      have hj'cast : input_j' = ((bitrange input_y.val 0 250 : ℕ) : Ecc.Fp)
          + ((2 ^ 130 : ℕ) : Ecc.Fp) - ((tPNat : ℕ) : Ecc.Fp) := by
        -- avoid the truncating `Nat` subtraction by adding `tPNat` back: `j'.val + t_P = j + 2^130`.
        have hj'nat : input_j'.val + tPNat = bitrange input_y.val 0 250 + 2 ^ 130 := by omega
        have hyj : input_j' = ((input_j'.val : ℕ) : Ecc.Fp) :=
          (ZMod.natCast_rightInverse input_j').symm
        have hcast := congrArg (Nat.cast (R := Ecc.Fp)) hj'nat
        push_cast at hcast ⊢
        rw [hyj]
        linear_combination hcast
      rw [hj, tP_eq, hj'cast]; ring
    · -- k3·k2 = 0
      rcases (show bitrange input_y.val 254 1 = 0 ∨ bitrange input_y.val 254 1 = 1 from by
        have := bitrange_lt input_y.val 254 1; omega) with h | h
      · rw [hk3, h]; simp
      · rw [hk2, (high_bit_canonical hyval h).1]; simp
    · -- k3·z13J = 0
      rcases (show bitrange input_y.val 254 1 = 0 ∨ bitrange input_y.val 254 1 = 1 from by
        have := bitrange_lt input_y.val 254 1; omega) with h | h
      · rw [hk3, h]; simp
      · rw [hz13, high_bit_z13_zero hyval h]; simp
    · -- k3·z13J' = 0
      rcases (show bitrange input_y.val 254 1 = 0 ∨ bitrange input_y.val 254 1 = 1 from by
        have := bitrange_lt input_y.val 254 1; omega) with h | h
      · rw [hk3, h]; simp
      · rw [hz13']
        have hlt : input_j'.val < 2 ^ 130 := by
          rw [hj']; exact (high_bit_canonical hyval h).2.2
        rw [Nat.div_eq_of_lt hlt]; simp

end YCanonicity.Gate

end Orchard.NoteCommit
