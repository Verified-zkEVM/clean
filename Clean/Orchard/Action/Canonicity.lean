import Clean.Circuit
import Clean.Gadgets.Boolean
import Clean.Orchard.Action.CanonicityTheorems
import Clean.Utils.Tactics
import Clean.Utils.Tactics.ProvableStructDeriving

/-!
# NoteCommit canonicity gates

Custom-gate `FormalAssertion`s enforcing prime-field canonicity of the decomposed note
fields (`orchard note_commit.rs` `*_canonicity`, `y_canonicity`).
-/

namespace Orchard.Action.NoteCommit

open Orchard.Specs (bitrange bitrange_lt bitrange_add)
open CompElliptic.Fields.Pasta (PALLAS_BASE_CARD)

namespace GdCanonicity.Gate

structure Row (F : Type) where
  gdX : F
  b0 : F
  b1 : F
  a : F
  aPrime : F
  z13A : F
  z13APrime : F
deriving ProvableStruct

def Spec (row : Row Fp) : Prop :=
  row.gdX = row.a + row.b0 * OfNat.ofNat (2 ^ 250) + row.b1 * OfNat.ofNat (2 ^ 254) ∧
    row.aPrime = row.a + OfNat.ofNat (2 ^ 130) - Ecc.tP ∧
    (row.b1 = 0 ∨ row.b0 = 0) ∧
    (row.b1 = 0 ∨ row.z13A = 0) ∧
    (row.b1 = 0 ∨ row.z13APrime = 0)

def main (row : Var Row Fp) : Circuit Fp Unit := do
  assertZero (row.a + row.b0 * OfNat.ofNat (2 ^ 250) +
    row.b1 * OfNat.ofNat (2 ^ 254) - row.gdX)
  assertZero (row.a + Expression.const ((2 ^ 130 : ℕ) : Fp) -
    Expression.const Ecc.tP - row.aPrime)
  assertZero (row.b1 * row.b0)
  assertZero (row.b1 * row.z13A)
  assertZero (row.b1 * row.z13APrime)

def circuit : FormalAssertion Fp Row where
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

end GdCanonicity.Gate

namespace PkdCanonicity.Gate

structure Row (F : Type) where
  pkdX : F
  b3 : F
  d0 : F
  c : F
  b3CPrime : F
  z13C : F
  z14B3CPrime : F
deriving ProvableStruct

def Spec (row : Row Fp) : Prop :=
  row.pkdX = row.b3 + row.c * 16 + row.d0 * OfNat.ofNat (2 ^ 254) ∧
    row.b3CPrime = row.b3 + row.c * 16 + OfNat.ofNat (2 ^ 140) - Ecc.tP ∧
    (row.d0 = 0 ∨ row.z13C = 0) ∧
    (row.d0 = 0 ∨ row.z14B3CPrime = 0)

def main (row : Var Row Fp) : Circuit Fp Unit := do
  assertZero (row.b3 + row.c * 16 + row.d0 * OfNat.ofNat (2 ^ 254) - row.pkdX)
  assertZero (row.b3 + row.c * 16 + Expression.const ((2 ^ 140 : ℕ) : Fp) -
    Expression.const Ecc.tP - row.b3CPrime)
  assertZero (row.d0 * row.z13C)
  assertZero (row.d0 * row.z14B3CPrime)

def circuit : FormalAssertion Fp Row where
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

end PkdCanonicity.Gate

namespace ValueCanonicity.Gate

structure Row (F : Type) where
  value : F
  d2 : F
  d3 : F
  e0 : F
deriving ProvableStruct

def Spec (row : Row Fp) : Prop :=
  row.value = row.d2 + row.d3 * 256 + row.e0 * 288230376151711744

def main (row : Var Row Fp) : Circuit Fp Unit := do
  assertZero (row.d2 + row.d3 * 256 + row.e0 * 288230376151711744 - row.value)

def circuit : FormalAssertion Fp Row where
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

end ValueCanonicity.Gate

namespace RhoCanonicity.Gate

structure Row (F : Type) where
  rho : F
  e1 : F
  g0 : F
  f : F
  e1FPrime : F
  z13F : F
  z14E1FPrime : F
deriving ProvableStruct

def Spec (row : Row Fp) : Prop :=
  row.rho = row.e1 + row.f * 16 + row.g0 * OfNat.ofNat (2 ^ 254) ∧
    row.e1FPrime = row.e1 + row.f * 16 + OfNat.ofNat (2 ^ 140) - Ecc.tP ∧
    (row.g0 = 0 ∨ row.z13F = 0) ∧
    (row.g0 = 0 ∨ row.z14E1FPrime = 0)

def main (row : Var Row Fp) : Circuit Fp Unit := do
  assertZero (row.e1 + row.f * 16 + row.g0 * OfNat.ofNat (2 ^ 254) - row.rho)
  assertZero (row.e1 + row.f * 16 + Expression.const ((2 ^ 140 : ℕ) : Fp) -
    Expression.const Ecc.tP - row.e1FPrime)
  assertZero (row.g0 * row.z13F)
  assertZero (row.g0 * row.z14E1FPrime)

def circuit : FormalAssertion Fp Row where
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

end RhoCanonicity.Gate

namespace PsiCanonicity.Gate

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

def Spec (row : Row Fp) : Prop :=
  row.psi = row.g1 + row.g2 * 512 + row.h0 * OfNat.ofNat (2 ^ 249) +
    row.h1 * OfNat.ofNat (2 ^ 254) ∧
    row.g1G2Prime = row.g1 + row.g2 * 512 + OfNat.ofNat (2 ^ 130) - Ecc.tP ∧
    (row.h1 = 0 ∨ row.h0 = 0) ∧
    (row.h1 = 0 ∨ row.z13G = 0) ∧
    (row.h1 = 0 ∨ row.z13G1G2Prime = 0)

def main (row : Var Row Fp) : Circuit Fp Unit := do
  assertZero (row.g1 + row.g2 * 512 + row.h0 * OfNat.ofNat (2 ^ 249) +
    row.h1 * OfNat.ofNat (2 ^ 254) - row.psi)
  assertZero (row.g1 + row.g2 * 512 + Expression.const ((2 ^ 130 : ℕ) : Fp) -
    Expression.const Ecc.tP - row.g1G2Prime)
  assertZero (row.h1 * row.h0)
  assertZero (row.h1 * row.z13G)
  assertZero (row.h1 * row.z13G1G2Prime)

def circuit : FormalAssertion Fp Row where
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

end PsiCanonicity.Gate

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
def Assumptions (row : Row Fp) : Prop :=
  row.k0 = ((bitrange row.y.val 1 9 : ℕ) : Fp) ∧
    row.k2 = ((bitrange row.y.val 250 4 : ℕ) : Fp) ∧
    row.k3 = ((bitrange row.y.val 254 1 : ℕ) : Fp) ∧
    row.j = ((bitrange row.y.val 0 250 : ℕ) : Fp) ∧
    row.z1J = ((bitrange row.y.val 10 240 : ℕ) : Fp) ∧
    row.z13J = ((bitrange row.y.val 130 120 : ℕ) : Fp) ∧
    row.j'.val = bitrange row.y.val 0 250 + 2 ^ 130 - tPNat ∧
    row.z13J' = ((row.j'.val / 2 ^ 130 : ℕ) : Fp)

/-- The gate's payoff: `lsb` is the low (sign) bit of the `y` coordinate. -/
def Spec (row : Row Fp) : Prop :=
  IsLowBit row.y row.lsb

def main (row : Var Row Fp) : Circuit Fp Unit := do
  assertBool row.k3
  assertZero (row.j - (row.lsb + row.k0 * 2 + row.z1J * 1024))
  assertZero (row.y - (row.j + row.k2 * ((2 ^ 250 : ℕ) : Fp) +
    row.k3 * ((2 ^ 254 : ℕ) : Fp)))
  assertZero (row.j + Expression.const ((2 ^ 130 : ℕ) : Fp) -
    Expression.const Ecc.tP - row.j')
  assertZero (row.k3 * row.k2)
  assertZero (row.k3 * row.z13J)
  assertZero (row.k3 * row.z13J')

def circuit : FormalAssertion Fp Row where
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
    have hcast : ((bitrange input_y.val 0 250 : ℕ) : Fp)
        = ((bitrange input_y.val 0 1 : ℕ) : Fp)
          + 2 * ((bitrange input_y.val 1 9 : ℕ) : Fp)
          + 1024 * ((bitrange input_y.val 10 240 : ℕ) : Fp) := by
      rw [low_250_decomp]; push_cast; ring
    rw [hj, hk0, hz1J, hcast] at hj_eq
    linear_combination -hj_eq
  completeness := by
    circuit_proof_start
    obtain ⟨hk0, hk2, hk3, hj, hz1J, hz13, hj', hz13'⟩ := h_assumptions
    have hyval : input_y.val < PALLAS_BASE_CARD := ZMod.val_lt input_y
    have hyval255 : input_y.val < 2 ^ 255 := lt_trans hyval (by norm_num [PALLAS_BASE_CARD])
    -- `lsb` is the low bit of `y`, supplied by the `Spec`.
    have hlsb : input_lsb = ((bitrange input_y.val 0 1 : ℕ) : Fp) := by
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
      have hyv : input_y = ((input_y.val : ℕ) : Fp) :=
        (ZMod.natCast_rightInverse input_y).symm
      have hdcast : ((input_y.val : ℕ) : Fp)
          = ((bitrange input_y.val 0 250 : ℕ) : Fp)
            + ((bitrange input_y.val 250 4 : ℕ) : Fp) * ((2 ^ 250 : ℕ) : Fp)
            + ((bitrange input_y.val 254 1 : ℕ) : Fp) * ((2 ^ 254 : ℕ) : Fp) := by
        conv_lhs => rw [bit_decomp_255 hyval255]
        push_cast; ring
      linear_combination hyv + hdcast - hj - ((2 ^ 250 : ℕ) : Fp) * hk2
        - ((2 ^ 254 : ℕ) : Fp) * hk3
    · -- j' = j + 2^130 - t_P
      have htp : tPNat ≤ bitrange input_y.val 0 250 + 2 ^ 130 := by
        have h1 : tPNat < 2 ^ 130 := by norm_num [tPNat]
        omega
      have hj'cast : input_j' = ((bitrange input_y.val 0 250 : ℕ) : Fp)
          + ((2 ^ 130 : ℕ) : Fp) - ((tPNat : ℕ) : Fp) := by
        -- avoid the truncating `Nat` subtraction by adding `tPNat` back: `j'.val + t_P = j + 2^130`.
        have hj'nat : input_j'.val + tPNat = bitrange input_y.val 0 250 + 2 ^ 130 := by omega
        have hyj : input_j' = ((input_j'.val : ℕ) : Fp) :=
          (ZMod.natCast_rightInverse input_j').symm
        have hcast := congrArg (Nat.cast (R := Fp)) hj'nat
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

end Orchard.Action.NoteCommit
