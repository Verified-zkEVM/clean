import Mathlib.Analysis.Normed.Ring.Lemmas
import Clean.Utils.Field
import Mathlib.Data.Nat.Bitwise
def not64 (a : ℕ) : ℕ := a ^^^ 0xffffffffffffffff

def add32 (a b : ℕ) : ℕ := (a + b) % 2^32

def rotRight8 (x : Fin 256) (offset : Fin 8) : Fin 256 :=
  let low := x % (2^offset.val)
  let high := x / (2^offset.val)
  low * (2^(8 - offset.val)) + high

def rotLeft8 (x : Fin 256) (offset : Fin 8) : Fin 256 :=
  let low := x % (2^(8 - offset.val))
  let high := x / (2^(8 - offset.val))
  low * (2^offset.val) + high

def rotRight64 (x : ℕ) (offset : ℕ) : ℕ :=
  let offset := offset % 64
  let low := x % (2^offset)
  let high := x / (2^offset)
  low * (2^(64 - offset)) + high

def rotRight32 (x : ℕ) (offset : ℕ) : ℕ :=
  let offset := offset % 32
  let low := x % (2^offset)
  let high := x / (2^offset)
  low * (2^(32 - offset)) + high

def rotLeft64 (value : ℕ) (left : Fin 64) : ℕ:=
  let right := (64 - left) % 64
  rotRight64 value right

lemma rotLeft64_eq_rotRight64 (x : ℕ) (offset : Fin 64) :
    rotLeft64 x offset = rotRight64 x (-offset).val := by
  simp [rotLeft64]

theorem eq_of_mod_eq_and_div_eq (m : ℕ) {x y : ℕ} (mod : x % m = y % m) (div : x / m = y / m) : x = y := by
  rw [←Nat.mod_add_div x m, ←Nat.mod_add_div y m, mod, div]

theorem xor_eq_add {x : ℕ} (n : ℕ) (hx : x < 2^n) (y : ℕ) : x + 2^n * y = x ^^^ 2^n * y := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [add_comm, Nat.testBit_two_pow_mul_add _ hx, Nat.testBit_xor, Nat.testBit_two_pow_mul]
  by_cases hi : i < n
  · have : ¬(n ≤ i) := by linarith
    simp [this]
  · have : n ≤ i := by linarith
    replace hx : x < 2^i := by
      apply lt_of_lt_of_le hx
      exact Nat.pow_le_pow_of_le (a :=2) (by norm_num) this
    rw [Nat.testBit_lt_two_pow hx]
    simp [this]

theorem and_mul_two_pow {x y n : ℕ} : 2 ^ n * (x &&& y) =  2 ^ n * x &&&  2 ^ n * y := by
  simp only [mul_comm]
  exact Nat.bitwise_mul_two_pow

theorem xor_mul_two_pow {x y n : ℕ} : 2 ^ n * (x ^^^ y) =  2 ^ n * x ^^^  2 ^ n * y := by
  simp only [mul_comm]
  exact Nat.bitwise_mul_two_pow

lemma and_mul_two_pow_lt {n : ℕ} {x : ℕ} (hx : x < 2^n) (y : ℕ) : x &&& 2^n * y = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.zero_testBit, Nat.testBit_two_pow_mul]
  by_cases h : i < n
  · simp [h]
  · have : n ≤ i := by linarith
    replace hx : x < 2^i := by
      apply lt_of_lt_of_le hx
      exact Nat.pow_le_pow_of_le (a :=2) (by norm_num) this
    rw [Nat.testBit_lt_two_pow hx]
    simp

lemma and_xor_sum (x0 x1 y0 y1 : ℕ) (hx0 : x0 < 2^8) (hy0 : y0 < 2^8) :
  (x0 ^^^ (2^8 * x1)) &&& (y0 ^^^ (2^8 * y1)) = (x0 &&& y0) ^^^ 2^8 * (x1 &&& y1) := by
  simp only [Nat.and_xor_distrib_left, Nat.and_xor_distrib_right]
  have zero0 : 2 ^ 8 * x1 &&& y0 = 0 := by rw [Nat.and_comm]; apply and_mul_two_pow_lt hy0
  have zero1 : x0 &&& 2 ^ 8 * y1 = 0 := and_mul_two_pow_lt hx0 _
  rw [zero0, zero1, Nat.xor_zero, Nat.zero_xor]
  congr; symm
  exact and_mul_two_pow

theorem not64_eq_sub {x : ℕ} (x_lt : x < 2^64) :
    not64 x = 2^64 - 1 - x := by
  rw [not64]
  have h_u64 : (x.toUInt64 ^^^ 0xffffffffffffffff).toNat = (0xffffffffffffffff - x.toUInt64).toNat := by
    apply congrArg UInt64.toNat
    bv_decide
  rw [UInt64.toNat_xor, UInt64.toNat_sub_of_le, Nat.toUInt64, UInt64.toNat_ofNat_of_lt' x_lt] at h_u64
  exact h_u64
  rw [UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' x_lt]
  exact Nat.le_pred_of_lt x_lt

-- Bitwise AND theorems

/-- For binary values, 0 is the absorbing element for `&&&` -/
theorem and_zero_absorb (a : ℕ) :
    0 &&& a = 0 := by
  -- 0 &&& a = Nat.land 0 a = 0
  simp only [HAnd.hAnd, AndOp.and]
  -- land 0 a = 0
  simp only [Nat.land]
  apply Nat.bitwise_zero_left

/-- For binary values, 1 is the identity element for `&&&` -/
theorem and_one_id_binary (a : ℕ) (ha : a = 0 ∨ a = 1) :
    1 &&& a = a := by
  cases ha with
  | inl h0 => rw [h0]; rfl
  | inr h1 => rw [h1]; rfl
