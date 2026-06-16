import Clean.Circuit
import Clean.Gadgets.Boolean
import Clean.Orchard.Ecc
import Clean.Utils.Tactics
import Clean.Utils.Tactics.ProvableStructDeriving

/-!
# Orchard incoming viewing key commitment gate

Clean port of the Orchard `CommitIvk` custom gate.

Reference:
`orchard@0.14.0/src/circuit/commit_ivk.rs`
- `CommitIvk canonicity check`
- `gadgets::commit_ivk`

The top-level `circuit` models the arithmetic constraints enabled by the Halo2
`q_commit_ivk` selector, not the selector, row layout, Sinsemilla hash, lookup range
checks, or assignment machinery around the gate.
-/

namespace Orchard.Action.CommitIvk.Gate

variable {F : Type} [Field F]

private theorem mul_eq_zero_of_or {a b : F} (h : a = 0 ∨ b = 0) : a * b = 0 := by
  rcases h with h | h <;> rw [h] <;> simp

private theorem left_eq_of_add_neg_eq_zero {a b : F} (h : a + -b = 0) : a = b :=
  sub_eq_zero.mp (by simpa [sub_eq_add_neg] using h)

structure Input (F : Type) where
  ak : F
  nk : F
  a : F
  bWhole : F
  c : F
  dWhole : F
  b0 : F
  b1 : F
  b2 : F
  d0 : F
  d1 : F
  z13A : F
  z13C : F
  aPrime : F
  b2CPrime : F
  z13APrime : F
  z14B2CPrime : F
deriving ProvableStruct

def Spec (row : Input Fp) : Prop :=
  IsBool row.b1 ∧
    IsBool row.d1 ∧
    row.bWhole = row.b0 + row.b1 * 16 + row.b2 * 32 ∧
    row.dWhole = row.d0 + row.d1 * 512 ∧
    row.ak = row.a + row.b0 * OfNat.ofNat (2 ^ 250) +
      row.b1 * OfNat.ofNat (2 ^ 254) ∧
    row.nk = row.b2 + row.c * 32 + row.d0 * OfNat.ofNat (2 ^ 245) +
      row.d1 * OfNat.ofNat (2 ^ 254) ∧
    (row.b1 = 0 ∨ row.b0 = 0) ∧
    (row.b1 = 0 ∨ row.z13A = 0) ∧
    row.aPrime = row.a + OfNat.ofNat (2 ^ 130) - Ecc.tP ∧
    (row.b1 = 0 ∨ row.z13APrime = 0) ∧
    (row.d1 = 0 ∨ row.d0 = 0) ∧
    (row.d1 = 0 ∨ row.z13C = 0) ∧
    row.b2CPrime = row.b2 + row.c * 32 + OfNat.ofNat (2 ^ 140) - Ecc.tP ∧
    (row.d1 = 0 ∨ row.z14B2CPrime = 0)

def main (row : Var Input Fp) : Circuit Fp Unit := do
  assertBool row.b1
  assertBool row.d1
  assertZero (row.bWhole - (row.b0 + row.b1 * 16 + row.b2 * 32))
  assertZero (row.dWhole - (row.d0 + row.d1 * 512))
  assertZero (row.a + row.b0 * OfNat.ofNat (2 ^ 250) +
    row.b1 * OfNat.ofNat (2 ^ 254) - row.ak)
  assertZero (row.b2 + row.c * 32 + row.d0 * OfNat.ofNat (2 ^ 245) +
    row.d1 * OfNat.ofNat (2 ^ 254) - row.nk)
  assertZero (row.b1 * row.b0)
  assertZero (row.b1 * row.z13A)
  assertZero (row.a + Expression.const ((2 ^ 130 : ℕ) : Fp) -
    Expression.const Ecc.tP - row.aPrime)
  assertZero (row.b1 * row.z13APrime)
  assertZero (row.d1 * row.d0)
  assertZero (row.d1 * row.z13C)
  assertZero (row.b2 + row.c * 32 + Expression.const ((2 ^ 140 : ℕ) : Fp) -
    Expression.const Ecc.tP - row.b2CPrime)
  assertZero (row.d1 * row.z14B2CPrime)

def circuit : FormalAssertion Fp Input where
  name := "GATE CommitIvk canonicity check"
  main
  Spec := Spec
  soundness := by
    circuit_proof_start [Ecc.tP]
    rcases h_holds with
      ⟨hb1, hd1, hb, hd, hak, hnk, hb0, hz13A, haPrime, hz13APrime, hd0, hz13C,
        hb2CPrime, hz14B2CPrime⟩
    exact ⟨hb1, hd1,
      left_eq_of_add_neg_eq_zero hb, left_eq_of_add_neg_eq_zero hd,
      (left_eq_of_add_neg_eq_zero hak).symm, (left_eq_of_add_neg_eq_zero hnk).symm,
      mul_eq_zero.mp hb0, mul_eq_zero.mp hz13A,
      by simpa [sub_eq_add_neg] using (left_eq_of_add_neg_eq_zero haPrime).symm,
      mul_eq_zero.mp hz13APrime, mul_eq_zero.mp hd0, mul_eq_zero.mp hz13C,
      by simpa [sub_eq_add_neg] using (left_eq_of_add_neg_eq_zero hb2CPrime).symm,
      mul_eq_zero.mp hz14B2CPrime⟩
  completeness := by
    circuit_proof_start [Ecc.tP]
    rcases h_spec with
      ⟨hb1, hd1, hb, hd, hak, hnk, hb0, hz13A, haPrime, hz13APrime, hd0, hz13C,
        hb2CPrime, hz14B2CPrime⟩
    constructor
    · exact hb1
    constructor
    · exact hd1
    constructor
    · rw [hb]
      ring
    constructor
    · rw [hd]
      ring
    constructor
    · rw [hak]
      ring
    constructor
    · rw [hnk]
      ring
    constructor
    · exact mul_eq_zero_of_or hb0
    constructor
    · exact mul_eq_zero_of_or hz13A
    constructor
    · rw [haPrime]
      ring
    constructor
    · exact mul_eq_zero_of_or hz13APrime
    constructor
    · exact mul_eq_zero_of_or hd0
    constructor
    · exact mul_eq_zero_of_or hz13C
    constructor
    · rw [hb2CPrime]
      ring
    exact mul_eq_zero_of_or hz14B2CPrime

end Orchard.Action.CommitIvk.Gate
