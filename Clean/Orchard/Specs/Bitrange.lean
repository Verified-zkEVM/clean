import Mathlib.Tactic
import Clean.Orchard.Specs.Elliptic.Fields.Pasta

open CompElliptic.Fields.Pasta (Fp)

/-!
# Bit ranges of a natural number

`bitrange n start len` is the value of the `len`-bit field of `n` starting at bit
`start` (i.e. bits `start .. start+len-1`). It is the scalar atom underlying every
contiguous bit-slice that shows up in the canonicity proofs (and `Sinsemilla.chunksOf`
is just a list of `K`-aligned, `K`-wide `bitrange`s).
-/

namespace Orchard.Specs

/-- The Sinsemilla / lookup-range-check word width: bits per chunk (`= 10`).
Shared by `Sinsemilla.chunksOf` and `LookupRangeCheck`. -/
def K : ℕ := 10

/-- The value of the `len`-bit field of `n` starting at bit `start`. -/
def bitrange (n start len : ℕ) : ℕ := n / 2 ^ start % 2 ^ len

@[simp] theorem bitrange_lt (n start len : ℕ) : bitrange n start len < 2 ^ len :=
  Nat.mod_lt _ (by positivity)

/-- A number that already fits in `len` bits is its own low-`len`-bit field. -/
theorem bitrange_eq_of_lt {n len : ℕ} (h : n < 2 ^ len) : bitrange n 0 len = n := by
  simp only [bitrange, pow_zero, Nat.div_one, Nat.mod_eq_of_lt h]

/-- Slicing after a shift is slicing at the shifted offset. -/
theorem bitrange_div (n s t len : ℕ) :
    bitrange (n / 2 ^ s) t len = bitrange n (s + t) len := by
  simp only [bitrange, Nat.div_div_eq_div_mul, ← pow_add]

/-- Adjacent fields concatenate: the low `a+b` bits split into the low `a` bits plus the
next `b` bits scaled by `2^a`. -/
theorem bitrange_add (n start a b : ℕ) :
    bitrange n start (a + b) =
      bitrange n start a + 2 ^ a * bitrange n (start + a) b := by
  have hb : bitrange n (start + a) b = n / 2 ^ start / 2 ^ a % 2 ^ b := by
    simp only [bitrange, Nat.div_div_eq_div_mul, ← pow_add]
  simp only [bitrange] at *
  rw [hb]
  set m := n / 2 ^ start with hm
  have h1 : m % 2 ^ (a + b) / 2 ^ a = m / 2 ^ a % 2 ^ b := by
    rw [pow_add, Nat.mod_mul_right_div_self]
  have h2 : m % 2 ^ (a + b) % 2 ^ a = m % 2 ^ a :=
    Nat.mod_mod_of_dvd m (pow_dvd_pow 2 (Nat.le_add_right a b))
  rw [← Nat.div_add_mod (m % 2 ^ (a + b)) (2 ^ a), h1, h2]
  ring

/-- A field is unchanged by truncating the input above its top bit. -/
theorem bitrange_mod {n s len m : ℕ} (h : s + len ≤ m) :
    bitrange (n % 2 ^ m) s len = bitrange n s len := by
  have hs : s ≤ m := le_trans (Nat.le_add_right s len) h
  have hlen : len ≤ m - s := by omega
  simp only [bitrange]
  rw [show (2 : ℕ) ^ m = 2 ^ s * 2 ^ (m - s) by rw [← pow_add, Nat.add_sub_cancel' hs],
    Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 hlen)]

theorem cast_bitrange_val {start numBits : ℕ} (hNumBits : numBits ≤ 254) (value : Fp) :
    (((bitrange value.val start numBits : ℕ) : Fp)).val = bitrange value.val start numBits :=
  ZMod.val_natCast_of_lt (lt_trans (bitrange_lt _ _ _)
    (lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num) hNumBits)
      (by norm_num [Fp])))

end Orchard.Specs
