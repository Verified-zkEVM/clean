import Mathlib.Tactic
import Mathlib.Algebra.Field.ZMod
import Clean.Utils.Field

namespace Bitwise

theorem eq_of_mod_eq_and_div_eq (m : ℕ) {x y : ℕ} (mod : x % m = y % m) (div : x / m = y / m) : x = y := by
  rw [←Nat.mod_add_div x m, ←Nat.mod_add_div y m, mod, div]

theorem xor_eq_add {x : ℕ} (n : ℕ) (hx : x < 2^n) (y : ℕ) : x + 2^n * y = x ^^^ 2^n * y := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [add_comm, Nat.testBit_mul_pow_two_add _ hx, Nat.testBit_xor, Nat.testBit_mul_pow_two]
  by_cases hi : i < n
  · have : ¬(n ≤ i) := by linarith
    simp [this]
  · have : n ≤ i := by linarith
    replace hx : x < 2^i := by
      apply lt_of_lt_of_le hx
      exact Nat.pow_le_pow_of_le (a:=2) (by norm_num) this
    rw [Nat.testBit_lt_two_pow hx]
    simp [this]

theorem and_mul_two_pow {x y n : Nat} : 2 ^ n * (x &&& y) =  2 ^ n * x &&&  2 ^ n * y := by
  simp only [mul_comm]
  exact Nat.bitwise_mul_two_pow

theorem xor_mul_two_pow {x y n : Nat} : 2 ^ n * (x ^^^ y) =  2 ^ n * x ^^^  2 ^ n * y := by
  simp only [mul_comm]
  exact Nat.bitwise_mul_two_pow

lemma and_mul_pow_two_lt {n : ℕ} {x : ℕ} (hx : x < 2^n) (y : ℕ) : x &&& 2^n * y = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.zero_testBit, Nat.testBit_mul_pow_two]
  by_cases h : i < n
  · simp [h]
  · have : n ≤ i := by linarith
    replace hx : x < 2^i := by
      apply lt_of_lt_of_le hx
      exact Nat.pow_le_pow_of_le (a:=2) (by norm_num) this
    rw [Nat.testBit_lt_two_pow hx]
    simp

lemma and_xor_sum (x0 x1 y0 y1 : ℕ) (hx0 : x0 < 2^8) (hy0 : y0 < 2^8) :
  (x0 ^^^ (2^8 * x1)) &&& (y0 ^^^ (2^8 * y1)) = (x0 &&& y0) ^^^ 2^8 * (x1 &&& y1) := by
  simp only [Nat.and_xor_distrib_left, Nat.and_xor_distrib_right]
  have zero0 : 2 ^ 8 * x1 &&& y0 = 0 := by rw [Nat.and_comm]; apply and_mul_pow_two_lt hy0
  have zero1 : x0 &&& 2 ^ 8 * y1 = 0 := and_mul_pow_two_lt hx0 _
  rw [zero0, zero1, Nat.xor_zero, Nat.zero_xor]
  congr; symm
  exact and_mul_two_pow

def not64 (a : ℕ) : ℕ := a ^^^ 0xffffffffffffffff

theorem not64_eq_sub {x : ℕ} (x_lt : x < 2^64) :
    not64 x = 2^64 - 1 - x := by
  rw [not64]
  have h_u64 : (x.toUInt64 ^^^ 0xffffffffffffffff).toNat = (0xffffffffffffffff - x.toUInt64).toNat := by
    apply congrArg UInt64.toNat
    bv_decide
  rw [UInt64.toNat_xor, UInt64.toNat_sub_of_le, UInt64.toNat_ofNat_of_lt x_lt] at h_u64
  exact h_u64
  rw [UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt x_lt]
  exact Nat.le_pred_of_lt x_lt
end Bitwise
