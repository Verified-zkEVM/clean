module

public import Clean.Utils.FiniteField
public import CompPoly.Fields.Binary.BF64
public import Mathlib.Tactic.NormNum.Prime

@[expose] public section

/-!
# Binary fields

`BF64` is CompPoly's `GF(2^64)`, stored in a polynomial basis over `GF(2)`. Its `FiniteField`
embedding reads the 64 polynomial coefficients as the bits of a natural number.
-/

instance : FiniteField BF64 where
  val x := x.toBitVec.toNat
  fromNat n := BF64.ofBitVec (BitVec.ofNat 64 n)
  size := 2 ^ 64
  val_lt x := x.toBitVec.isLt
  val_injective _ _ h := BF64.ext (BitVec.eq_of_toNat_eq h)
  val_fromNat n hn := by simp [Nat.mod_eq_of_lt hn]
  val_zero := rfl
  val_one := rfl

namespace BF64

/-- The polynomial `X`, a primitive element: its powers are all nonzero elements. -/
def X : BF64 := ofBitVec 2#64

theorem orderOf_X : orderOf X = FiniteField.size BF64 - 1 := by
  change orderOf X = 2 ^ 64 - 1
  have h_prod : 2 ^ 64 - 1 = 3 * 5 * 17 * 257 * 641 * 65537 * 6700417 := by norm_num
  apply orderOf_eq_of_pow_and_pow_div_prime (by norm_num) (by decide +kernel)
  intro q hq hdvd
  rw [h_prod] at hdvd
  simp only [hq.dvd_mul] at hdvd
  have eq (r : ℕ) (hr : r.Prime) : q ∣ r → q = r := (Nat.prime_dvd_prime_iff_eq hq hr).mp
  rcases hdvd with (((((h | h) | h) | h) | h) | h) | h
  all_goals first
    | rw [eq 3 (by norm_num) h] | rw [eq 5 (by norm_num) h] | rw [eq 17 (by norm_num) h]
    | rw [eq 257 (by norm_num) h] | rw [eq 641 (by norm_num) h] | rw [eq 65537 (by norm_num) h]
    | rw [eq 6700417 (by norm_num) h]
  all_goals decide +kernel

end BF64
