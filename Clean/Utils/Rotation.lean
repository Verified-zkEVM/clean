import Clean.Utils.Bitwise
import Clean.Utils.Vector
import Mathlib.Data.Nat.Bitwise
import Clean.Utils.Bits

namespace Utils.Rotation
open Bits (toBits toBits_injective)

-- Theorems about 64-bit rotation

/--
  Our definition of right rotation of a 64-bit integer is equal to
  the one provided by `BitVec.rotateRight`
-/
def rotRight64_eq_bv_rotate (x : ℕ) (h : x < 2^64) (offset : ℕ) :
    rotRight64 x offset = (x.toUInt64.toBitVec.rotateRight offset).toNat := by
  simp only [rotRight64]
  simp only [BitVec.toNat_rotateRight]
  simp only [Nat.shiftLeft_eq, Nat.mul_mod, dvd_refl, Nat.mod_mod_of_dvd]
  simp only [Nat.mod_mod, UInt64.toNat_toBitVec]

  by_cases cond : (offset % 64 = 0)
  · simp [cond, pow_zero, Nat.mod_one, tsub_zero, Nat.reducePow, zero_mul, Nat.div_one,
    zero_add, Nat.shiftRight_zero, Nat.mod_self, mul_zero, Nat.zero_mod, Nat.or_zero]
    symm
    apply Nat.mod_eq_of_lt
    linarith

  · have h1 : 2^(64-offset%64) < 2^64 := by
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
      simp only [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat]
      apply Nat.mod_lt_of_lt
      apply Nat.mod_lt offset (by linarith)

    have offset_bv_pos : offset_bv > 0 := by
      simp only [Nat.toUInt64_eq, gt_iff_lt, offset_bv]
      have := Nat.pos_of_ne_zero cond
      rw [UInt64.lt_ofNat_iff]
      simp only [UInt64.toNat_zero]
      · assumption
      · simp [UInt64.size]
        have : offset % 64 < 64 := Nat.mod_lt offset (by linarith)
        linarith

    specialize h_sat offset_bv_lt offset_bv_pos
    apply_fun UInt64.toNat at h_sat

    simp only [UInt64.toNat_shiftLeft, UInt64.toNat_mod, UInt64.toNat_ofNat,
      x_bv, offset_bv] at h_sat
    simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.one_mod] at h_sat
    rw [Nat.mod_eq_of_lt h] at h_sat

    have h' : UInt64.ofNat (offset % 64) ≤ 64 := by
      have : offset % 64 < 64 := Nat.mod_lt offset (by linarith)
      rw [UInt64.ofNat_le_iff]
      · simp only [UInt64.reduceToNat]
        linarith
      · simp [UInt64.size]
        linarith
    rw [UInt64.toNat_sub_of_le _ _ h'] at h_sat
    simp only [UInt64.reduceToNat, UInt64.toNat_ofNat'] at h_sat

    have h_eq : offset % 64 % 2^64 = offset % 64 := by
      apply Nat.mod_eq_of_lt
      have : offset % 64 < 64 := Nat.mod_lt offset (by linarith)
      linarith
    rw [h_eq, Nat.mod_mod] at h_sat
    simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat', dvd_refl, Nat.mod_mod_of_dvd]

    rw [show x % 2^64 = x by
      apply Nat.mod_eq_of_lt
      linarith]

    have h_eq' : (64 - offset % 64) % 64 = 64 - offset % 64 := by
      apply Nat.mod_eq_of_lt
      have : offset % 64 < 64 := Nat.mod_lt offset (by linarith)
      simp only [tsub_lt_self_iff, Nat.ofNat_pos, true_and, gt_iff_lt]
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
      rw (occs:=.pos [4]) [eq]
      apply Nat.shiftLeft_lt
      rw [Nat.one_shiftLeft]
      apply Nat.mod_lt
      simp only [Nat.ofNat_pos, pow_pos]

    rw [h_eq3]

/--
  Alternative definition of rotRight64 using bitwise operations.
-/
lemma rotRight64_def (x : ℕ) (off : ℕ) (hx : x < 2^64) :
    rotRight64 x off = x >>> (off % 64) ||| x <<< (64 - off % 64) % 2 ^ 64 := by
  rw [rotRight64_eq_bv_rotate _ hx]
  simp only [Nat.toUInt64_eq, BitVec.toNat_rotateRight, UInt64.toNat_toBitVec, UInt64.toNat_ofNat']
  rw [show x % 2^64 = x by apply Nat.mod_eq_of_lt hx]

/--
  The rotation operation is invariant when taking the offset modulo 64.
-/
lemma rotRight64_off_mod_64 (x : ℕ) (off1 off2 : ℕ) (h : off1 = off2 % 64) :
    rotRight64 x off1 = rotRight64 x off2 := by
  simp only [rotRight64]
  rw [←h]
  have h' : off2 % 64 < 64 := Nat.mod_lt off2 (by linarith)
  rw [←h] at h'
  rw [Nat.mod_eq_of_lt h']

lemma rotRight64_fin (x : ℕ) (offset : Fin 64) :
    rotRight64 x offset.val = x % (2^offset.val) * (2^(64-offset.val)) + x / (2^offset.val) := by
  simp only [rotRight64]
  rw [Nat.mod_eq_of_lt offset.is_lt]

/--
  Testing a bit of the result of a rotation in the range [0, r % 64) is equivalent to testing
  the bit of the original number in the range [i, r % 64 + i).
-/
lemma rotRight64_testBit_of_lt (x r i : ℕ) (h : x < 2^64) (hi : i < 64 - r % 64) :
    (rotRight64 x r).testBit i = x.testBit (r % 64 + i) := by
  rw [rotRight64_def _ _ h, Nat.testBit_or, Nat.testBit_shiftRight, Nat.testBit_mod_two_pow,
    Nat.testBit_shiftLeft]
  have h_i : 64 - r % 64 ≤ 64 := by apply Nat.sub_le
  have h_i' : i < 64 := by linarith
  simp [h_i']
  omega

/--
  Testing a bit of the result of a rotation in the range [64 - r % 64, 64) is equivalent to
  testing the bit of the original number in the range [i - (64 - r % 64), i).
-/
lemma rotRight64_testBit_of_ge (x r i : ℕ) (h : x < 2^64) (hi : i ≥ 64 - r % 64) :
    (rotRight64 x r).testBit i = (decide (i < 64) && x.testBit (i - (64 - r % 64))) := by
  rw [rotRight64_def _ _ h, Nat.testBit_or, Nat.testBit_mod_two_pow]
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

lemma rotRight64_testBit (x r i : ℕ) (h : x < 2^64) :
    (rotRight64 x r).testBit i =
    if i < 64 - r % 64 then
      x.testBit (r % 64 + i)
    else (decide (i < 64) && x.testBit (i - (64 - r % 64))) := by

  split
  · rw [rotRight64_testBit_of_lt]
    repeat omega
  · rw [rotRight64_testBit_of_ge]
    repeat omega

/--
  The bits of the result of a rotation are the rotated bits of the input
-/
theorem rotRight64_toBits (x r : ℕ) (h : x < 2^64):
    toBits 64 (rotRight64 x r) = (toBits 64 x).rotate r := by
  simp [toBits, Vector.rotate]
  ext i hi
  · simp
  simp only [Vector.size_toArray, Vector.getElem_toArray,
    Vector.getElem_mapRange, List.getElem_toArray, List.getElem_rotate] at ⊢ hi
  rw [rotRight64_testBit]
  simp only [hi, decide_true, Bool.true_and, Bool.ite_eq_true_distrib,
    Vector.length_toList, Vector.getElem_toList, Vector.getElem_mapRange]
  split <;> (congr; omega)
  linarith

theorem rotRight64_lt (x r : ℕ) (h : x < 2^64) :
    rotRight64 x r < 2^64 := by
  rw [rotRight64_def _ _ h]
  have := Nat.shiftRight_le x (r % 64)
  apply Nat.or_lt_two_pow <;> omega

/--
  Rotating a 64-bit value by `n` bits and then by `m` bits is the same
  as rotating it by `n + m` bits.
-/
theorem rotRight64_composition (x n m : ℕ) (h : x < 2^64) :
    rotRight64 (rotRight64 x n) m = rotRight64 x (n + m) := by
  have h1 : (rotRight64 (rotRight64 x n) m) < 2^64 := by
    repeat apply rotRight64_lt
    assumption

  have h2 : (rotRight64 x (n + m)) < 2^64 := by
    apply rotRight64_lt
    assumption

  -- suffices to show equality over bits
  suffices toBits 64 (rotRight64 (rotRight64 x n) m) = toBits 64 (rotRight64 x (n + m)) by
    exact toBits_injective 64 h1 h2 this

  -- rewrite rotation over bits
  rw [rotRight64_toBits _ _ h,
    rotRight64_toBits _ _ (by apply rotRight64_lt; assumption),
    rotRight64_toBits _ _ h]

  -- now this is easy, it is just rotation composition over vectors
  rw [Vector.rotate_rotate]

-- Theorems about 32-bit rotation

/--
  Our definition of right rotation of a 32-bit integer is equal to
  the one provided by `BitVec.rotateRight`
-/
def rotRight32_eq_bv_rotate (x : ℕ) (h : x < 2^32) (offset : ℕ) :
    rotRight32 x offset = (x.toUInt32.toBitVec.rotateRight offset).toNat := by
  simp only [rotRight32]
  simp only [BitVec.toNat_rotateRight]
  simp only [Nat.shiftLeft_eq, Nat.mul_mod, dvd_refl, Nat.mod_mod_of_dvd]
  simp only [Nat.mod_mod, UInt32.toNat_toBitVec]

  by_cases cond : (offset % 32 = 0)
  · simp [cond, pow_zero, Nat.mod_one, tsub_zero, Nat.reducePow, zero_mul, Nat.div_one,
    zero_add, Nat.shiftRight_zero, Nat.mod_self, mul_zero, Nat.zero_mod, Nat.or_zero]
    symm
    apply Nat.mod_eq_of_lt
    linarith

  · have h1 : 2^(32-offset%32) < 2^32 := by
      apply Nat.pow_lt_pow_of_lt
      · linarith
      · simp only [tsub_lt_self_iff, Nat.ofNat_pos, true_and]
        simp [Nat.ne_zero_iff_zero_lt] at cond
        assumption
    rw [Nat.mod_eq_of_lt h1, Nat.shiftRight_eq_div_pow]
    have low_lt : x / 2 ^ (offset % 32) < 2 ^ (32 - offset % 32) := by
      rw [Nat.div_lt_iff_lt_mul (by apply Nat.two_pow_pos)]
      rw [←Nat.pow_add, Nat.sub_add_cancel (by
        have : offset % 32 < 32 := Nat.mod_lt offset (by linarith)
        linarith)]
      linarith
    rw [mul_comm, Nat.two_pow_add_eq_or_of_lt low_lt, Nat.or_comm]
    congr
    · simp only [Nat.toUInt32_eq, UInt32.toNat_ofNat', Nat.reducePow]
      symm
      apply Nat.mod_eq_of_lt
      assumption
    rw [Nat.mul_comm]
    rw [←Nat.shiftLeft_eq, ←Nat.shiftLeft_eq, ←Nat.one_shiftLeft]

    let x_bv := x.toUInt32
    let offset_bv := (offset % 32).toUInt32
    have h_sat : offset_bv < 32 → offset_bv > 0 →
        (x_bv % 1<<<offset_bv) <<< (32 - offset_bv) = x_bv <<< (32 - offset_bv) := by
      bv_decide

    have offset_bv_lt : offset_bv < 32 := by
      simp only [offset_bv]
      simp only [UInt32.lt_iff_toNat_lt, UInt32.toNat_ofNat]
      apply Nat.mod_lt_of_lt
      apply Nat.mod_lt offset (by linarith)

    have offset_bv_pos : offset_bv > 0 := by
      simp only [Nat.toUInt32_eq, gt_iff_lt, offset_bv]
      have := Nat.pos_of_ne_zero cond
      rw [UInt32.lt_ofNat_iff]
      simp only [UInt32.toNat_zero]
      · assumption
      · simp [UInt32.size]
        have : offset % 32 < 32 := Nat.mod_lt offset (by linarith)
        linarith

    specialize h_sat offset_bv_lt offset_bv_pos
    apply_fun UInt32.toNat at h_sat

    simp only [UInt32.toNat_shiftLeft, UInt32.toNat_mod, UInt32.toNat_ofNat,
      x_bv, offset_bv] at h_sat
    simp only [Nat.toUInt32_eq, UInt32.toNat_ofNat', Nat.one_mod] at h_sat
    rw [Nat.mod_eq_of_lt h] at h_sat

    have h' : UInt32.ofNat (offset % 32) ≤ 32 := by
      have : offset % 32 < 32 := Nat.mod_lt offset (by linarith)
      rw [UInt32.ofNat_le_iff]
      · simp only [UInt32.reduceToNat]
        linarith
      · simp [UInt32.size]
        linarith
    rw [UInt32.toNat_sub_of_le _ _ h'] at h_sat
    simp only [UInt32.reduceToNat, UInt32.toNat_ofNat'] at h_sat

    have h_eq : offset % 32 % 2^32 = offset % 32 := by
      apply Nat.mod_eq_of_lt
      have : offset % 32 < 32 := Nat.mod_lt offset (by linarith)
      linarith
    rw [h_eq, Nat.mod_mod] at h_sat
    simp only [Nat.toUInt32_eq, UInt32.toNat_ofNat', dvd_refl, Nat.mod_mod_of_dvd]

    rw [show x % 2^32 = x by
      apply Nat.mod_eq_of_lt
      linarith]

    have h_eq' : (32 - offset % 32) % 32 = 32 - offset % 32 := by
      apply Nat.mod_eq_of_lt
      have : offset % 32 < 32 := Nat.mod_lt offset (by linarith)
      simp only [tsub_lt_self_iff, Nat.ofNat_pos, true_and, gt_iff_lt]
      exact Nat.pos_of_ne_zero cond
    rw [h_eq'] at h_sat
    rw [←h_sat]

    have h_eq2 : (1 <<< (offset % 32)) % 2^32 = (1 <<< (offset % 32)) := by
      apply Nat.mod_eq_of_lt
      rw [Nat.one_shiftLeft]
      apply Nat.pow_lt_pow_of_lt
      linarith
      apply Nat.mod_lt
      linarith
    rw [h_eq2]

    have h_eq3 : (x % 1 <<< (offset % 32)) <<< (32 - offset % 32) % 2 ^ 32 =
        (x % 1 <<< (offset % 32)) <<< (32 - offset % 32) := by
      apply Nat.mod_eq_of_lt
      have eq : 32 = (offset % 32) + (32 - (offset % 32)) := by
        rw [Nat.add_sub_of_le]
        apply Nat.le_of_lt
        apply Nat.mod_lt
        linarith
      rw (occs:=.pos [4]) [eq]
      apply Nat.shiftLeft_lt
      rw [Nat.one_shiftLeft]
      apply Nat.mod_lt
      simp only [Nat.ofNat_pos, pow_pos]

    rw [h_eq3]

/--
  Alternative definition of rotRight32 using bitwise operations.
-/
lemma rotRight32_def (x : ℕ) (off : ℕ) (hx : x < 2^32) :
    rotRight32 x off = x >>> (off % 32) ||| x <<< (32 - off % 32) % 2 ^ 32 := by
  rw [rotRight32_eq_bv_rotate _ hx]
  simp only [Nat.toUInt32_eq, BitVec.toNat_rotateRight, UInt32.toNat_toBitVec, UInt32.toNat_ofNat']
  rw [show x % 2^32 = x by apply Nat.mod_eq_of_lt hx]

/--
  The rotation operation is invariant when taking the offset modulo 32.
-/
lemma rotRight32_off_mod_32 (x : ℕ) (off1 off2 : ℕ) (h : off1 = off2 % 32) :
    rotRight32 x off1 = rotRight32 x off2 := by
  simp only [rotRight32]
  rw [←h]
  have h' : off2 % 32 < 32 := Nat.mod_lt off2 (by linarith)
  rw [←h] at h'
  rw [Nat.mod_eq_of_lt h']

lemma rotRight32_fin (x : ℕ) (offset : Fin 32) :
    rotRight32 x offset.val = x % (2^offset.val) * (2^(32-offset.val)) + x / (2^offset.val) := by
  simp only [rotRight32]
  rw [Nat.mod_eq_of_lt offset.is_lt]

/--
  Testing a bit of the result of a rotation in the range [0, r % 32) is equivalent to testing
  the bit of the original number in the range [i, r % 32 + i).
-/
lemma rotRight32_testBit_of_lt (x r i : ℕ) (h : x < 2^32) (hi : i < 32 - r % 32) :
    (rotRight32 x r).testBit i = x.testBit (r % 32 + i) := by
  rw [rotRight32_def _ _ h, Nat.testBit_or, Nat.testBit_shiftRight, Nat.testBit_mod_two_pow,
    Nat.testBit_shiftLeft]
  have h_i : 32 - r % 32 ≤ 32 := by apply Nat.sub_le
  have h_i' : i < 32 := by linarith
  simp [h_i']
  omega

/--
  Testing a bit of the result of a rotation in the range [32 - r % 32, 32) is equivalent to
  testing the bit of the original number in the range [i - (32 - r % 32), i).
-/
lemma rotRight32_testBit_of_ge (x r i : ℕ) (h : x < 2^32) (hi : i ≥ 32 - r % 32) :
    (rotRight32 x r).testBit i = (decide (i < 32) && x.testBit (i - (32 - r % 32))) := by
  rw [rotRight32_def _ _ h, Nat.testBit_or, Nat.testBit_mod_two_pow]
  suffices (x >>> (r % 32)).testBit i = false by
    simp [this]
    by_cases h : i < 32 <;> simp [h]; omega

  simp only [Nat.testBit_shiftRight]
  apply Nat.testBit_lt_two_pow
  have : 2^32 ≤ 2^(r % 32 + i) := by
    apply Nat.pow_le_pow_right
    · linarith
    omega
  linarith

lemma rotRight32_testBit (x r i : ℕ) (h : x < 2^32) :
    (rotRight32 x r).testBit i =
    if i < 32 - r % 32 then
      x.testBit (r % 32 + i)
    else (decide (i < 32) && x.testBit (i - (32 - r % 32))) := by

  split
  · rw [rotRight32_testBit_of_lt]
    repeat omega
  · rw [rotRight32_testBit_of_ge]
    repeat omega

/--
  The bits of the result of a rotation are the rotated bits of the input
-/
theorem rotRight32_toBits (x r : ℕ) (h : x < 2^32):
    toBits 32 (rotRight32 x r) = (toBits 32 x).rotate r := by
  simp [toBits, Vector.rotate]
  ext i hi
  · simp
  simp only [Vector.size_toArray, Vector.getElem_toArray,
    Vector.getElem_mapRange, List.getElem_toArray, List.getElem_rotate] at ⊢ hi
  rw [rotRight32_testBit]
  simp only [hi, decide_true, Bool.true_and, Bool.ite_eq_true_distrib,
    Vector.length_toList, Vector.getElem_toList, Vector.getElem_mapRange]
  split <;> (congr; omega)
  linarith

theorem rotRight32_lt (x r : ℕ) (h : x < 2^32) :
    rotRight32 x r < 2^32 := by
  rw [rotRight32_def _ _ h]
  have := Nat.shiftRight_le x (r % 32)
  apply Nat.or_lt_two_pow <;> omega

/--
  Rotating a 32-bit value by `n` bits and then by `m` bits is the same
  as rotating it by `n + m` bits.
-/
theorem rotRight32_composition (x n m : ℕ) (h : x < 2^32) :
    rotRight32 (rotRight32 x n) m = rotRight32 x (n + m) := by
  have h1 : (rotRight32 (rotRight32 x n) m) < 2^32 := by
    repeat apply rotRight32_lt
    assumption

  have h2 : (rotRight32 x (n + m)) < 2^32 := by
    apply rotRight32_lt
    assumption

  -- suffices to show equality over bits
  suffices toBits 32 (rotRight32 (rotRight32 x n) m) = toBits 32 (rotRight32 x (n + m)) by
    exact toBits_injective 32 h1 h2 this

  -- rewrite rotation over bits
  rw [rotRight32_toBits _ _ h,
    rotRight32_toBits _ _ (by apply rotRight32_lt; assumption),
    rotRight32_toBits _ _ h]

  -- now this is easy, it is just rotation composition over vectors
  rw [Vector.rotate_rotate]

-- helpful lemmas for {32, 64}-bit rotation with offset in [0, 7]

lemma two_power_val {p : ℕ} {offset : Fin 8} [p_large_enough: Fact (p > 2^16 + 2^8)] :
    ((2 ^ (8 - offset.val) % 256 : ℕ) : F p).val = 2 ^ (8 - offset.val) % 256 := by
  rw [ZMod.val_natCast]
  apply Nat.mod_eq_of_lt
  have h : 2 ^ (8 - offset.val) % 256 < 256 := by apply Nat.mod_lt; linarith
  linarith [h, p_large_enough.elim]

lemma mul_mod256_off {offset : ℕ} (ho : offset < 8) (x i : ℕ) (h : i > 0):
    (x * 256^i) % 2^offset = 0 := by
  rw [Nat.mul_mod, Nat.pow_mod]
  repeat (
    rcases ho with _ | ho
    try simp only [zero_add, Nat.reducePow, Nat.reduceMod, Nat.zero_pow h, Nat.zero_mod, mul_zero]
  )

lemma Nat.pow_minus_one_mul {x y : ℕ} (hy : y > 0) : x ^ y = x * x ^ (y - 1) := by
  nth_rw 2 [←Nat.pow_one x]
  rw [←Nat.pow_add, Nat.add_sub_of_le (by linarith [hy])]

lemma divides_256_two_power {offset : ℕ} (ho : offset < 8) {x i : ℕ} (h : i > 0):
    (2^offset) ∣ x * (256 ^ i) := by
  rw [show 256 = 2^8 by rfl, ←Nat.pow_mul]
  apply Nat.dvd_mul_left_of_dvd
  apply Nat.pow_dvd_pow
  linarith

lemma div_256_two_power {offset : ℕ} (ho : offset < 8) {i : ℕ} (h : i > 0):
    256^i / 2^offset = 256^(i-1) * 2^(8-offset) := by
  rw [show 256 = 2^8 by rfl, ←Nat.pow_mul, Nat.pow_div]
  rw [←Nat.pow_mul, ←Nat.pow_add]
  rw [Nat.mul_sub_left_distrib, Nat.mul_one]
  rw [Nat.sub_add_sub_cancel]
  repeat linarith

lemma mul_div_256_off {offset : ℕ} (ho : offset < 8) {x : ℕ} (i : ℕ) (h : i > 0):
    (x * 256^i) / 2^offset = x * 256^(i-1) * 2^(8-offset) := by
  rw [Nat.mul_div_assoc, div_256_two_power ho h]
  rw [show 256=2^8 by rfl, ←Nat.pow_mul]
  ac_rfl
  rw [show 256=2^8 by rfl, ←Nat.pow_mul]
  apply Nat.pow_dvd_pow
  linarith

lemma two_off_eq_mod (offset : Fin 8) (h : offset.val ≠ 0):
    (2 ^ (8-offset.val) % 256) = 2 ^ (8-offset.val) := by
  apply Nat.mod_eq_of_lt
  fin_cases offset <;>
    first
    | contradiction
    | simp

lemma shifted_decomposition_eq {offset : ℕ} (ho : offset < 8) {x1 x2 : ℕ} :
    (x1 / 2 ^ offset + x2 % 2 ^ offset * 2 ^ (8-offset)) * 256 =
    (2^offset * (x1 / 2^offset) + (x2 % 2^offset) * 256) * 2^(8-offset) := by
  ring_nf
  simp only [Nat.add_left_inj]
  rw [Nat.mul_assoc, ←Nat.pow_add, Nat.add_sub_of_le (by linarith)]
  rfl

lemma shifted_decomposition_eq' {offset : ℕ} (ho : offset < 8) {x1 x2 i : ℕ} (hi : i > 0) :
    (x1 / 2 ^ offset + x2 % 2 ^ offset * 2 ^ (8-offset)) * 256^i =
    (2^offset * (x1 / 2^offset) + (x2 % 2^offset) * 256) * 2^(8-offset) * 256^(i-1) := by
  rw [Nat.pow_minus_one_mul hi, ←Nat.mul_assoc, shifted_decomposition_eq ho]

lemma shifted_decomposition_eq'' {offset : ℕ} (ho : offset < 8) {x1 x2 i : ℕ} (hi : i > 0) :
    (x1 / 2 ^ offset + x2 % 2 ^ offset * 2 ^ (8-offset)) * 256^i =
    (2^offset * (x1 / 2^offset) * 2^(8-offset) * 256^(i-1) +
    (x2 % 2^offset) * 2^(8-offset) * 256^i) := by
  rw [shifted_decomposition_eq' ho hi]
  ring_nf
  rw [Nat.mul_assoc _ _ 256, Nat.mul_comm _ 256, Nat.pow_minus_one_mul hi]

lemma soundness_simp {offset : ℕ} {x y : ℕ} :
    x % 2 ^ offset * 2 ^ (8-offset) * y + 2 ^ offset * (x / 2 ^ offset) * 2 ^ (8-offset) * y =
    x * y * 2^ (8-offset) := by
  rw [Nat.mul_assoc, Nat.mul_assoc, ←Nat.add_mul, add_comm, Nat.div_add_mod]
  ac_rfl

lemma soundness_simp' {offset : ℕ} {x : ℕ} :
    x % 2 ^ offset * 2 ^ (8-offset) + 2 ^ offset * (x / 2 ^ offset) * 2 ^ (8-offset) =
    x * 2^ (8-offset) := by
  rw [←Nat.mul_one (x % 2 ^ offset * 2 ^ (8 - offset))]
  rw [←Nat.mul_one (2 ^ offset * (x / 2 ^ offset) * 2 ^ (8 - offset))]
  rw [soundness_simp, Nat.mul_one]

lemma two_power_byte {p : ℕ} {offset : Fin 8} :
    ZMod.val ((2 ^ (8 - offset.val) % 256 : ℕ) : F p) < 256 := by
  rw [ZMod.val_natCast]
  apply Nat.mod_lt_of_lt
  apply Nat.mod_lt
  linarith

end Utils.Rotation
