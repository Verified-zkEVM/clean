import Clean.Utils.Field
import Clean.Utils.Bitwise
import Clean.Utils.Rotation
import Clean.Types.U32
import Clean.Gadgets.ByteDecomposition.ByteDecomposition


variable {p : ℕ} [Fact p.Prime]
variable [p_large_enough: Fact (p > 2^16 + 2^8)]

namespace Gadgets.Rotation32.Theorems
open Bitwise (rot_right32)
open Gadgets.ByteDecomposition.Theorems (byte_decomposition_lift)
open Utils.Rotation (mul_mod_256_off mul_div_256_off divides_256_two_power
  two_power_val two_power_byte two_off_eq_mod shifted_decomposition_eq shifted_decomposition_eq'
  shifted_decomposition_eq'' soundness_simp soundness_simp')

def rot_right32_eq_bv_rotate (x : ℕ) (h : x < 2^32) (offset : ℕ) :
    rot_right32 x offset = (x.toUInt64.toBitVec.rotateRight offset).toNat := by
  sorry

theorem rot_right_composition (x n m : ℕ) (h : x < 2^32) :
      rot_right32 (rot_right32 x n) m = rot_right32 x (n + m) := by
  rw [rot_right32_eq_bv_rotate _ h,
    rot_right32_eq_bv_rotate _ h,
    rot_right32_eq_bv_rotate _ (by sorry)]

  sorry

lemma h_mod32 {offset : Fin 8} {x0 x1 x2 x3 : ℕ} :
    (x0 + x1 * 256 + x2 * 256 ^ 2 + x3 * 256 ^ 3) %
      2 ^ offset.val = x0 % 2 ^ offset.val := by
  simp only [pow_one, Nat.add_mod, dvd_refl, Nat.mod_mod_of_dvd, gt_iff_lt, Nat.ofNat_pos,
    mul_mod_256_off, add_zero]
  rw [←Nat.pow_one 256, Nat.mod_mod, Nat.mod_mod, mul_mod_256_off _ _ _ (by linarith)]
  simp only [add_zero, dvd_refl, Nat.mod_mod_of_dvd]

lemma h_div32 {offset : Fin 8} {x0 x1 x2 x3: ℕ} :
    (x0 + x1 * 256 + x2 * 256 ^ 2 + x3 * 256 ^ 3) / 2 ^ offset.val
    = x0 / 2^offset.val + x1 * 2^(8 - offset.val) + x2 * 256 * 2^(8 - offset.val) +
    x3 * 256 ^ 2 * 2^(8 - offset.val) := by
  rw [←Nat.pow_one 256]
  repeat rw [Nat.add_div_of_dvd_left (by apply divides_256_two_power; linarith)]

  rw [mul_div_256_off 1 (by simp only [gt_iff_lt, Nat.lt_one_iff, pos_of_gt])]
  rw [mul_div_256_off 2 (by simp only [gt_iff_lt, Nat.ofNat_pos])]
  rw [mul_div_256_off 3 (by simp only [gt_iff_lt, Nat.ofNat_pos])]
  simp only [tsub_self, pow_zero, mul_one, Nat.add_one_sub_one, pow_one, Nat.reducePow,
    Nat.add_left_inj]

lemma h_x0_const32 {offset : Fin 8} :
    2 ^ (8 - offset.val) * 256^3 = 2^(32 - offset.val) := by
  rw [show 256 = 2^8 by rfl, ←Nat.pow_mul, ←Nat.pow_add, add_comm]
  simp only [Nat.reduceMul, Nat.ofNat_pos, ne_eq, OfNat.ofNat_ne_one, not_false_eq_true,
    pow_right_inj₀]
  simp only [Fin.is_le', ← Nat.add_sub_assoc, Nat.reduceAdd]



theorem rotation32_bits_soundness (offset : Fin 8) {
      x0 x1 x2 x3
      y0 y1 y2 y3
      x0_l x1_l x2_l x3_l
      x0_h x1_h x2_h x3_h : F p
    }
    (h_x0 : x0.val < 256)
    (h_x1 : x1.val < 256)
    (h_x2 : x2.val < 256)
    (h_x3 : x3.val < 256)
    (h_x0_l : x0_l.val = x0.val % 2 ^ offset.val)
    (h_x0_h : x0_h.val = x0.val / 2 ^ offset.val)
    (h_x1_l : x1_l.val = x1.val % 2 ^ offset.val)
    (h_x1_h : x1_h.val = x1.val / 2 ^ offset.val)
    (h_x2_l : x2_l.val = x2.val % 2 ^ offset.val)
    (h_x2_h : x2_h.val = x2.val / 2 ^ offset.val)
    (h_x3_l : x3_l.val = x3.val % 2 ^ offset.val)
    (h_x3_h : x3_h.val = x3.val / 2 ^ offset.val)
    (eq0 : x1_l * ↑(2 ^ (8 - offset.val) % 256 : ℕ) + x0_h + -y0 = 0)
    (eq1 : x2_l * ↑(2 ^ (8 - offset.val) % 256 : ℕ) + x1_h + -y1 = 0)
    (eq2 : x3_l * ↑(2 ^ (8 - offset.val) % 256 : ℕ) + x2_h + -y2 = 0)
    (eq3 : x0_l * ↑(2 ^ (8 - offset.val) % 256 : ℕ) + x3_h + -y3 = 0):
    let x_val := x0.val + x1.val * 256 + x2.val * 256 ^ 2 + x3.val * 256 ^ 3
    let y_val := y0.val + y1.val * 256 + y2.val * 256 ^ 2 + y3.val * 256 ^ 3
    y_val = (x_val) % 2 ^ (offset.val % 32) * 2 ^ (32 - offset.val % 32) + (x_val) / 2 ^ (offset.val % 32) := by

  rw [add_comm (_ * _)] at eq0 eq1 eq2 eq3

  -- lift every reconstruction constraint to its value form
  have x0_l_byte : x0_l.val < 256 := by rw [h_x0_l]; apply Nat.mod_lt_of_lt; assumption
  have x0_h_byte : x0_h.val < 256 := by rw [h_x0_h]; apply Nat.div_lt_of_lt; assumption
  have x1_l_byte : x1_l.val < 256 := by rw [h_x1_l]; apply Nat.mod_lt_of_lt; assumption
  have x1_h_byte : x1_h.val < 256 := by rw [h_x1_h]; apply Nat.div_lt_of_lt; assumption
  have x2_l_byte : x2_l.val < 256 := by rw [h_x2_l]; apply Nat.mod_lt_of_lt; assumption
  have x2_h_byte : x2_h.val < 256 := by rw [h_x2_h]; apply Nat.div_lt_of_lt; assumption
  have x3_l_byte : x3_l.val < 256 := by rw [h_x3_l]; apply Nat.mod_lt_of_lt; assumption
  have x3_h_byte : x3_h.val < 256 := by rw [h_x3_h]; apply Nat.div_lt_of_lt; assumption

  replace eq0 := byte_decomposition_lift x0_h_byte x1_l_byte two_power_byte eq0
  replace eq1 := byte_decomposition_lift x1_h_byte x2_l_byte two_power_byte eq1
  replace eq2 := byte_decomposition_lift x2_h_byte x3_l_byte two_power_byte eq2
  replace eq3 := byte_decomposition_lift x3_h_byte x0_l_byte two_power_byte eq3

  -- simplify the goal
  simp only [two_power_val, ZMod.val_natCast] at eq0 eq1 eq2 eq3
  rw [eq0, eq1, eq2, eq3]
  dsimp only

  have offset_mod_64 : offset.val % 32 = offset.val := by
    apply Nat.mod_eq_of_lt
    linarith [offset.is_lt]

  simp [h_x0_l, h_x0_h, h_x1_l, h_x1_h, h_x2_l, h_x2_h, h_x3_l, h_x3_h, offset_mod_64, -Nat.reducePow]

  rw [h_mod32]
  -- if the offset is zero, then it is trivial: it is a special case since
  -- in that case the rotation is a no-op
  by_cases h_offset : offset.val = 0
  · rw [h_offset]
    simp only [Fin.isValue, Fin.val_zero, pow_zero, Nat.div_one, Nat.mod_one, tsub_zero,
      Nat.reducePow, Nat.mod_self, mul_zero, add_zero, zero_mul, zero_add, Nat.add_left_inj]
  · rw [two_off_eq_mod _ (by simp only [ne_eq, Fin.val_eq_zero_iff, Fin.isValue, h_offset,
      not_false_eq_true])]
    rw [h_div32]
    -- proof technique: we care about only what happens to x0, all "internal" terms remain
    -- the same, and are just divided by 2^offset.val
    rw [shifted_decomposition_eq]
    repeat rw [shifted_decomposition_eq'' (by simp only [gt_iff_lt, Nat.ofNat_pos])]
    simp only [Nat.add_one_sub_one, pow_one, add_mul, add_assoc]
    rw [←add_assoc _ _ (_ * 256 ^ 3), soundness_simp]
    nth_rw 4 [←add_assoc]
    rw [Nat.mul_right_comm _ 256, soundness_simp]
    nth_rw 2 [←add_assoc]
    rw [Nat.mul_right_comm _ 256, soundness_simp']
    rw [mul_assoc (x0.val % 2 ^ offset.val), h_x0_const32]
    ac_rfl

end Gadgets.Rotation32.Theorems
