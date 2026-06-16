import Clean.Circuit
import Clean.Gadgets.Boolean
import Clean.Orchard.Ecc
import Clean.Orchard.Specs.Bitrange
import Clean.Utils.Tactics

/-!
# NoteCommit canonicity theorems

Foundational bit-decomposition / Pallas-base-modulus canonicity facts shared by the
note-commitment gates.  Stated over `Orchard.Specs.bitrange` and the modulus, with no
reference to any particular circuit cell.
-/

namespace Orchard.Action.NoteCommit

variable {F : Type} [Field F]

theorem mul_eq_zero_of_or {a b : F} (h : a = 0 ∨ b = 0) : a * b = 0 := by
  rcases h with h | h <;> rw [h] <;> simp

theorem left_eq_of_add_neg_eq_zero {a b : F} (h : a + -b = 0) : a = b :=
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
def IsLowBit (y lsb : Fp) : Prop :=
  lsb = ((if y.val.testBit 0 then 1 else 0 : ℕ) : Fp)

theorem nat_mod_two_isBool (n : ℕ) : IsBool (((n % 2 : ℕ) : Fp)) := by
  have hlt : n % 2 < 2 := Nat.mod_lt _ (by norm_num)
  interval_cases n % 2 <;> simp [IsBool]

theorem isLowBit_iff_mod_two {y lsb : Fp} :
    IsLowBit y lsb ↔ lsb = ((y.val % 2 : ℕ) : Fp) := by
  have key : (if y.val.testBit 0 then (1 : ℕ) else 0) = y.val % 2 := by
    rw [Nat.testBit_zero]
    rcases Nat.mod_two_eq_zero_or_one y.val with hm | hm <;> simp [hm]
  rw [IsLowBit, key]

/-- `Ecc.tP` as the cast of the natural number `tPNat`. -/
theorem tP_eq : Ecc.tP = ((tPNat : ℕ) : Fp) := by
  rw [Ecc.tP, tPNat]; norm_num

/-- A 1-bit field slice is Boolean. -/
theorem bitrange_one_isBool (n start : ℕ) :
    IsBool ((bitrange n start 1 : ℕ) : Fp) := by
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

end Orchard.Action.NoteCommit
