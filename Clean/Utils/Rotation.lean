import Clean.Utils.Bitwise
import Clean.Utils.Vector
import Mathlib.Data.Nat.Bitwise
import Clean.Utils.Bits

namespace Utils.Rotation
open Bitwise (rot_right64)
open Bits (to_bits to_bits_injective)
/--
  Our definition of right rotation of a 64-bit integer is equal to
  the one provided by `BitVec.rotateRight`
-/
def rot_right64_eq_bv_rotate (x : ℕ) (h : x < 2^64) (offset : ℕ) :
    rot_right64 x offset = (x.toUInt64.toBitVec.rotateRight offset).toNat := by
  simp only [rot_right64]
  simp only [BitVec.toNat_rotateRight]
  simp only [Nat.shiftLeft_eq, Nat.mul_mod, dvd_refl, Nat.mod_mod_of_dvd]
  simp only [Nat.mod_mod, UInt64.toNat_toBitVec, UInt64.toNat_ofNat]

  by_cases cond : (offset % 64 = 0)
  · simp [cond, pow_zero, Nat.mod_one, tsub_zero, Nat.reducePow, zero_mul, Nat.div_one,
    zero_add, Nat.shiftRight_zero, Nat.mod_self, mul_zero, Nat.zero_mod, Nat.or_zero]
    symm
    apply Nat.mod_eq_of_lt
    linarith

  · have h1 : 2^(64 - offset%64) < 2^64 := by
      apply Nat.pow_lt_pow_of_lt
      · linarith
      · simp only [tsub_lt_self_iff, Nat.ofNat_pos, true_and]
        simp [Nat.ne_zero_iff_zero_lt] at cond
        assumption
    rw [Nat.mod_eq_of_lt h1, Nat.shiftRight_eq_div_pow]
    have low_lt : x / 2 ^ (offset % 64) < 2 ^ (64 - offset % 64) := by
      rw [Nat.div_lt_iff_lt_mul (by apply Nat.two_pow_pos)]
      rw [←Nat.pow_add, Nat.sub_add_cancel (by
        have : offset % 64 < 64 := Nat.mod_lt offset (by linarith)
        linarith)]
      linarith
    rw [mul_comm, Nat.two_pow_add_eq_or_of_lt low_lt, Nat.or_comm]
    congr
    · simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.reducePow]
      symm
      apply Nat.mod_eq_of_lt
      assumption
    rw [Nat.mul_comm]
    rw [←Nat.shiftLeft_eq, ←Nat.shiftLeft_eq, ←Nat.one_shiftLeft]

    let x_bv := x.toUInt64
    let offset_bv := (offset % 64).toUInt64
    have h_sat : offset_bv < 64 → offset_bv > 0 →
        (x_bv % 1<<<offset_bv) <<< (64 - offset_bv) = x_bv <<< (64 - offset_bv) := by
      bv_decide

    have offset_bv_lt : offset_bv < 64 := by
      simp only [offset_bv]
      simp only [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat, UInt64.reduceToNat]
      apply Nat.mod_lt_of_lt
      apply Nat.mod_lt offset (by linarith)

    have offset_bv_pos : offset_bv > 0 := by
      simp only [Nat.toUInt64_eq, gt_iff_lt, offset_bv]
      have := Nat.pos_of_ne_zero cond
      rw [UInt64.lt_ofNat_iff]
      simp only [UInt64.toNat_zero, offset_bv]
      · assumption
      · simp [UInt64.size]
        have : offset % 64 < 64 := Nat.mod_lt offset (by linarith)
        linarith

    specialize h_sat offset_bv_lt offset_bv_pos
    apply_fun UInt64.toNat at h_sat

    simp only [UInt64.toNat_shiftLeft, UInt64.toNat_mod, UInt64.toNat_ofNat,
      UInt64.reduceToNat, x_bv, offset_bv] at h_sat
    simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.one_mod, Nat.reduceDvd,
      Nat.mod_mod_of_dvd, dvd_refl, offset_bv, x_bv] at h_sat
    rw [Nat.mod_eq_of_lt h] at h_sat

    have h' : UInt64.ofNat (offset % 64) ≤ 64 := by
      have : offset % 64 < 64 := Nat.mod_lt offset (by linarith)
      rw [UInt64.ofNat_le_iff]
      · simp only [UInt64.reduceToNat, ge_iff_le, offset_bv, x_bv]
        linarith
      · simp [UInt64.size]
        linarith
    rw [UInt64.toNat_sub_of_le _ _ h'] at h_sat
    simp only [Nat.reduceDvd, Nat.mod_mod_of_dvd, dvd_refl, UInt64.reduceToNat,
      UInt64.toNat_ofNat', offset_bv, x_bv] at h_sat

    have h_eq : offset % 64 % 2^64 = offset % 64 := by
      apply Nat.mod_eq_of_lt
      have : offset % 64 < 64 := Nat.mod_lt offset (by linarith)
      linarith
    rw [h_eq, Nat.mod_mod] at h_sat
    simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat', dvd_refl, Nat.mod_mod_of_dvd,
      offset_bv, x_bv]

    rw [show x % 2^64 = x by
      apply Nat.mod_eq_of_lt
      linarith]

    have h_eq' : (64 - offset % 64) % 64 = 64 - offset % 64 := by
      apply Nat.mod_eq_of_lt
      have : offset % 64 < 64 := Nat.mod_lt offset (by linarith)
      simp only [tsub_lt_self_iff, Nat.ofNat_pos, true_and, gt_iff_lt, offset_bv, x_bv]
      exact Nat.pos_of_ne_zero cond
    rw [h_eq'] at h_sat
    rw [←h_sat]

    have h_eq2 : (1 <<< (offset % 64)) % 2^64 = (1 <<< (offset % 64)) := by
      apply Nat.mod_eq_of_lt
      rw [Nat.one_shiftLeft]
      apply Nat.pow_lt_pow_of_lt
      linarith
      apply Nat.mod_lt
      linarith
    rw [h_eq2]

    have h_eq3 : (x % 1 <<< (offset % 64)) <<< (64 - offset % 64) % 2 ^ 64 =
        (x % 1 <<< (offset % 64)) <<< (64 - offset % 64) := by
      apply Nat.mod_eq_of_lt
      have eq : 64 = (offset % 64) + (64 - (offset % 64)) := by
        rw [Nat.add_sub_of_le]
        apply Nat.le_of_lt
        apply Nat.mod_lt
        linarith
      rw (occs:= .pos [4]) [eq]
      apply Nat.shiftLeft_lt
      rw [Nat.one_shiftLeft]
      apply Nat.mod_lt
      simp only [gt_iff_lt, Nat.ofNat_pos, pow_pos, offset_bv, x_bv]

    rw [h_eq3]

/--
  Alternative definicion of rot_right64 using bitwise operations.
-/
lemma rot_right64_def (x : ℕ) (off : ℕ) (hx : x < 2^64) :
    rot_right64 x off = x >>> (off % 64) ||| x <<< (64 - off % 64) % 2 ^ 64 := by
  rw [rot_right64_eq_bv_rotate _ hx]
  simp only [Nat.toUInt64_eq, BitVec.toNat_rotateRight, UInt64.toNat_toBitVec, UInt64.toNat_ofNat']
  rw [show x % 2^64 = x by apply Nat.mod_eq_of_lt hx]

/--
  The rotation operation is invariant when taking the offset modulo 64.
-/
lemma rot_right_64_off_mod_64 (x : ℕ) (off1 off2 : ℕ) (h : off1 = off2 % 64) :
    rot_right64 x off1 = rot_right64 x off2 := by
  simp only [rot_right64]
  rw [←h]
  have h' : off2 % 64 < 64 := Nat.mod_lt off2 (by linarith)
  rw [←h] at h'
  rw [Nat.mod_eq_of_lt h']

lemma rot_right64_fin (x : ℕ) (offset : Fin 64) :
    rot_right64 x offset.val = x % (2^offset.val) * (2^(64 - offset.val)) + x / (2^offset.val) := by
  simp only [rot_right64]
  rw [Nat.mod_eq_of_lt offset.is_lt]

/--
  Testing a bit of the result of a rotation in the range [0, r % 64) is equivalent to testing
  the bit of the original number in the range [i, r % 64 + i).
-/
lemma rot_right64_testBit_of_lt (x r i : ℕ) (h : x < 2^64) (hi : i < 64 - r % 64) :
    (rot_right64 x r).testBit i = x.testBit (r % 64 + i) := by
  rw [rot_right64_def _ _ h, Nat.testBit_or, Nat.testBit_shiftRight, Nat.testBit_mod_two_pow,
    Nat.testBit_shiftLeft]
  have h_i : 64 - r % 64 ≤ 64 := by apply Nat.sub_le
  have h_i' : i < 64 := by linarith
  simp [h_i']
  omega

/--
  Testing a bit of the result of a rotation in the range [64 - r % 64, 64) is equivalent to
  testing the bit of the original number in the range [i - (64 - r % 64), i).
-/
lemma rot_right64_testBit_of_ge (x r i : ℕ) (h : x < 2^64) (hi : i ≥ 64 - r % 64) :
    (rot_right64 x r).testBit i = (decide (i < 64) && x.testBit (i - (64 - r % 64))) := by
  rw [rot_right64_def _ _ h, Nat.testBit_or, Nat.testBit_mod_two_pow]
  suffices (x >>> (r % 64)).testBit i = false by
    simp [this]
    by_cases h : i < 64 <;> simp [h]; omega

  simp only [Nat.testBit_shiftRight]
  apply Nat.testBit_lt_two_pow
  have : 2^64 ≤ 2^(r % 64 + i) := by
    apply Nat.pow_le_pow_right
    · linarith
    omega
  linarith

lemma rot_right64_testBit (x r i : ℕ) (h : x < 2^64) :
    (rot_right64 x r).testBit i =
    if i < 64 - r % 64 then
      x.testBit (r % 64 + i)
    else (decide (i < 64) && x.testBit (i - (64 - r % 64))) := by

  split
  · rw [rot_right64_testBit_of_lt]
    repeat omega
  · rw [rot_right64_testBit_of_ge]
    repeat omega


/--
  The bits of the result of a rotation are the rotated bits of the input
-/
theorem rot_right64_to_bits (x r : ℕ) (h : x < 2^64):
    to_bits 64 (rot_right64 x r) = (to_bits 64 x).rotate r := by
  simp [to_bits, Vector.rotate]
  ext i hi
  · simp
  simp at ⊢ hi
  rw [rot_right64_testBit]
  simp [List.getElem_rotate, hi]
  split <;> (congr; omega)
  linarith


theorem rot_right64_lt (x r : ℕ) (h : x < 2^64) :
    rot_right64 x r < 2^64 := by
  rw [rot_right64_def _ _ h]
  have := Nat.shiftRight_le x (r % 64)
  apply Nat.or_lt_two_pow <;> omega

/--
  Rotating a 64-bit value by `n` bits and then by `m` bits is the same
  as rotating it by `n + m` bits.
-/
theorem rot_right64_composition (x n m : ℕ) (h : x < 2^64) :
    rot_right64 (rot_right64 x n) m = rot_right64 x (n + m) := by
  have h1 : (rot_right64 (rot_right64 x n) m) < 2^64 := by
    repeat apply rot_right64_lt
    assumption

  have h2 : (rot_right64 x (n + m)) < 2^64 := by
    apply rot_right64_lt
    assumption

  -- suffices to show equality over bits
  suffices to_bits 64 (rot_right64 (rot_right64 x n) m) = to_bits 64 (rot_right64 x (n + m)) by
    exact to_bits_injective 64 h1 h2 this

  -- rewrite rotation over bits
  rw [rot_right64_to_bits _ _ h,
    rot_right64_to_bits _ _ (by apply rot_right64_lt; assumption),
    rot_right64_to_bits _ _ h]

  -- now this is easy, it is just rotation composition over vectors
  rw [Vector.rotate_rotate]

end Utils.Rotation
