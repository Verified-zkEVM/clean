import Mathlib.Tactic
import Mathlib.Algebra.Field.ZMod
import Clean.Utils.Field

namespace Bytes
def split_two_bytes (i : Fin (256 * 256)) : Fin 256 × Fin 256 :=
  let x := i.val / 256
  let y := i.val % 256
  have x_lt : x < 256 := by simp [x, Nat.div_lt_iff_lt_mul]
  have y_lt : y < 256 := Nat.mod_lt i.val (by norm_num)
  (⟨ x, x_lt ⟩, ⟨ y, y_lt ⟩)

def concat_two_bytes (x y : Fin 256) : Fin (256 * 256) :=
  let i := x.val * 256 + y.val
  have i_lt : i < 256 * 256 := by
    unfold i
    linarith [x.is_lt, y.is_lt]
  ⟨ i, i_lt ⟩

theorem concat_split (x y : Fin 256) : split_two_bytes (concat_two_bytes x y) = (x, y) := by
  dsimp [split_two_bytes, concat_two_bytes]
  ext
  simp only
  rw [mul_comm]
  have h := Nat.mul_add_div (by norm_num : 256 > 0) x.val y.val
  rw [h]
  simp
  simp only [Nat.mul_add_mod_of_lt y.is_lt]

section
variable {p : ℕ}  [Fact p.Prime] [p_large_enough: Fact (p > 512)]

def from_byte (x: Fin 256) : F p :=
  FieldUtils.nat_to_field x.val (by linarith [x.is_lt, p_large_enough.elim])

lemma from_byte_lt (x: Fin 256) : (from_byte (p:=p) x).val < 256 := by
  dsimp [from_byte]
  rw [FieldUtils.val_of_nat_to_field_eq]
  exact x.is_lt

lemma from_byte_eq (x : F p) (x_lt : x.val < 256) : from_byte ⟨ x.val, x_lt ⟩ = x := by
  dsimp [from_byte]
  apply FieldUtils.nat_to_field_of_val_eq_iff

lemma from_byte_cast_eq {z: F p} (z_lt : z.val < 256) : from_byte z.cast = z := by
  simp only [from_byte]
  have : (z.cast : Fin 256).val = z.val := ZMod.val_cast_eq_val_of_lt z_lt
  simp only [this]
  apply FieldUtils.nat_to_field_of_val_eq_iff
end
end Bytes

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

end Bitwise
