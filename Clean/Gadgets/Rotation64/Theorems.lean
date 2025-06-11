import Clean.Utils.Field
import Clean.Utils.Bitwise
import Clean.Utils.Rotation
import Clean.Types.U64
import Clean.Gadgets.ByteDecomposition.ByteDecomposition

variable {p : ℕ} [Fact p.Prime]
variable [p_large_enough: Fact (p > 2^16 + 2^8)]

namespace Gadgets.Rotation64.Theorems
open Bitwise (rot_right64)
open Gadgets.ByteDecomposition.Theorems (byte_decomposition_lift)
open Utils.Rotation (mul_mod_256_off mul_div_256_off divides_256_two_power
  two_power_val two_power_byte two_off_eq_mod shifted_decomposition_eq shifted_decomposition_eq'
  shifted_decomposition_eq'' soundness_simp soundness_simp')


def rot_right8 (x : Fin 256) (offset : Fin 8) : Fin 256 :=
  let low := x % (2^offset.val)
  let high := x / (2^offset.val)
  low * (2^(8 - offset.val)) + high

def rot_left8 (x : Fin 256) (offset : Fin 8) : Fin 256 :=
  let low := x % (2^(8 - offset.val))
  let high := x / (2^(8 - offset.val))
  low * (2^offset.val) + high


lemma h_mod {offset : Fin 8} {x0 x1 x2 x3 x4 x5 x6 x7 : ℕ} :
    (x0 + x1 * 256 + x2 * 256 ^ 2 + x3 * 256 ^ 3 + x4 * 256 ^ 4 + x5 * 256 ^ 5 + x6 * 256 ^ 6 + x7 * 256 ^ 7) %
      2 ^ offset.val = x0 % 2 ^ offset.val := by
  simp only [pow_one, Nat.add_mod, dvd_refl, Nat.mod_mod_of_dvd, gt_iff_lt, Nat.ofNat_pos,
    mul_mod_256_off, add_zero]
  rw [←Nat.pow_one 256, Nat.mod_mod, Nat.mod_mod, mul_mod_256_off _ _ _ (by linarith)]
  simp only [add_zero, dvd_refl, Nat.mod_mod_of_dvd]

lemma h_div {offset : Fin 8} {x0 x1 x2 x3 x4 x5 x6 x7 : ℕ} :
    (x0 + x1 * 256 + x2 * 256 ^ 2 + x3 * 256 ^ 3 + x4 * 256 ^ 4 + x5 * 256 ^ 5 + x6 * 256 ^ 6 + x7 * 256 ^ 7) / 2 ^ offset.val
    = x0 / 2^offset.val + x1 * 2^(8 - offset.val) + x2 * 256 * 2^(8 - offset.val) +
    x3 * 256 ^ 2 * 2^(8 - offset.val) + x4 * 256 ^ 3 * 2^(8 - offset.val) +
    x5 * 256 ^ 4 * 2^(8 - offset.val) + x6 * 256 ^ 5 * 2^(8 - offset.val) +
    x7 * 256 ^ 6 * 2^(8 - offset.val) := by
  rw [←Nat.pow_one 256]
  repeat rw [Nat.add_div_of_dvd_left (by apply divides_256_two_power; linarith)]

  rw [mul_div_256_off 1 (by simp only [gt_iff_lt, Nat.lt_one_iff, pos_of_gt])]
  rw [mul_div_256_off 2 (by simp only [gt_iff_lt, Nat.ofNat_pos])]
  rw [mul_div_256_off 3 (by simp only [gt_iff_lt, Nat.ofNat_pos])]
  rw [mul_div_256_off 4 (by simp only [gt_iff_lt, Nat.ofNat_pos])]
  rw [mul_div_256_off 5 (by simp only [gt_iff_lt, Nat.ofNat_pos])]
  rw [mul_div_256_off 6 (by simp only [gt_iff_lt, Nat.ofNat_pos])]
  rw [mul_div_256_off 7 (by simp only [gt_iff_lt, Nat.ofNat_pos])]
  simp only [tsub_self, pow_zero, mul_one, Nat.add_one_sub_one, pow_one, Nat.reducePow,
    Nat.add_left_inj]

lemma h_x0_const {offset : Fin 8} :
    2 ^ (8 - offset.val) * 256^7 = 2^(64 - offset.val) := by
  rw [show 256 = 2^8 by rfl, ←Nat.pow_mul, ←Nat.pow_add, add_comm]
  simp only [Nat.reduceMul, Nat.ofNat_pos, ne_eq, OfNat.ofNat_ne_one, not_false_eq_true,
    pow_right_inj₀]
  simp only [Fin.is_le', ← Nat.add_sub_assoc, Nat.reduceAdd]


theorem rotation64_bits_soundness (offset : Fin 8) {
      x0 x1 x2 x3 x4 x5 x6 x7
      y0 y1 y2 y3 y4 y5 y6 y7
      x0_l x1_l x2_l x3_l x4_l x5_l x6_l x7_l
      x0_h x1_h x2_h x3_h x4_h x5_h x6_h x7_h : F p
    }
    (h_x0 : x0.val < 256)
    (h_x1 : x1.val < 256)
    (h_x2 : x2.val < 256)
    (h_x3 : x3.val < 256)
    (h_x4 : x4.val < 256)
    (h_x5 : x5.val < 256)
    (h_x6 : x6.val < 256)
    (h_x7 : x7.val < 256)
    (h_x0_l : x0_l.val = x0.val % 2 ^ offset.val)
    (h_x0_h : x0_h.val = x0.val / 2 ^ offset.val)
    (h_x1_l : x1_l.val = x1.val % 2 ^ offset.val)
    (h_x1_h : x1_h.val = x1.val / 2 ^ offset.val)
    (h_x2_l : x2_l.val = x2.val % 2 ^ offset.val)
    (h_x2_h : x2_h.val = x2.val / 2 ^ offset.val)
    (h_x3_l : x3_l.val = x3.val % 2 ^ offset.val)
    (h_x3_h : x3_h.val = x3.val / 2 ^ offset.val)
    (h_x4_l : x4_l.val = x4.val % 2 ^ offset.val)
    (h_x4_h : x4_h.val = x4.val / 2 ^ offset.val)
    (h_x5_l : x5_l.val = x5.val % 2 ^ offset.val)
    (h_x5_h : x5_h.val = x5.val / 2 ^ offset.val)
    (h_x6_l : x6_l.val = x6.val % 2 ^ offset.val)
    (h_x6_h : x6_h.val = x6.val / 2 ^ offset.val)
    (h_x7_l : x7_l.val = x7.val % 2 ^ offset.val)
    (h_x7_h : x7_h.val = x7.val / 2 ^ offset.val)
    (eq0 : x1_l * ↑(2 ^ (8 - offset.val) % 256 : ℕ) + x0_h + -y0 = 0)
    (eq1 : x2_l * ↑(2 ^ (8 - offset.val) % 256 : ℕ) + x1_h + -y1 = 0)
    (eq2 : x3_l * ↑(2 ^ (8 - offset.val) % 256 : ℕ) + x2_h + -y2 = 0)
    (eq3 : x4_l * ↑(2 ^ (8 - offset.val) % 256 : ℕ) + x3_h + -y3 = 0)
    (eq4 : x5_l * ↑(2 ^ (8 - offset.val) % 256 : ℕ) + x4_h + -y4 = 0)
    (eq5 : x6_l * ↑(2 ^ (8 - offset.val) % 256 : ℕ) + x5_h + -y5 = 0)
    (eq6 : x7_l * ↑(2 ^ (8 - offset.val) % 256 : ℕ) + x6_h + -y6 = 0)
    (eq7 : x0_l * ↑(2 ^ (8 - offset.val) % 256 : ℕ) + x7_h + -y7 = 0):
    let x_val := x0.val + x1.val * 256 + x2.val * 256 ^ 2 + x3.val * 256 ^ 3 + x4.val * 256 ^ 4 +
      x5.val * 256 ^ 5 + x6.val * 256 ^ 6 + x7.val * 256 ^ 7
    let y_val := y0.val + y1.val * 256 + y2.val * 256 ^ 2 + y3.val * 256 ^ 3 + y4.val * 256 ^ 4 +
      y5.val * 256 ^ 5 + y6.val * 256 ^ 6 + y7.val * 256 ^ 7
    y_val = (x_val) % 2 ^ (offset.val % 64) * 2 ^ (64 - offset.val % 64) + (x_val) / 2 ^ (offset.val % 64) := by

  rw [add_comm (_ * _)] at eq0 eq1 eq2 eq3 eq4 eq5 eq6 eq7

  -- lift every reconstruction constraint to its value form
  have x0_l_byte : x0_l.val < 256 := by rw [h_x0_l]; apply Nat.mod_lt_of_lt; assumption
  have x0_h_byte : x0_h.val < 256 := by rw [h_x0_h]; apply Nat.div_lt_of_lt; assumption
  have x1_l_byte : x1_l.val < 256 := by rw [h_x1_l]; apply Nat.mod_lt_of_lt; assumption
  have x1_h_byte : x1_h.val < 256 := by rw [h_x1_h]; apply Nat.div_lt_of_lt; assumption
  have x2_l_byte : x2_l.val < 256 := by rw [h_x2_l]; apply Nat.mod_lt_of_lt; assumption
  have x2_h_byte : x2_h.val < 256 := by rw [h_x2_h]; apply Nat.div_lt_of_lt; assumption
  have x3_l_byte : x3_l.val < 256 := by rw [h_x3_l]; apply Nat.mod_lt_of_lt; assumption
  have x3_h_byte : x3_h.val < 256 := by rw [h_x3_h]; apply Nat.div_lt_of_lt; assumption
  have x4_l_byte : x4_l.val < 256 := by rw [h_x4_l]; apply Nat.mod_lt_of_lt; assumption
  have x4_h_byte : x4_h.val < 256 := by rw [h_x4_h]; apply Nat.div_lt_of_lt; assumption
  have x5_l_byte : x5_l.val < 256 := by rw [h_x5_l]; apply Nat.mod_lt_of_lt; assumption
  have x5_h_byte : x5_h.val < 256 := by rw [h_x5_h]; apply Nat.div_lt_of_lt; assumption
  have x6_l_byte : x6_l.val < 256 := by rw [h_x6_l]; apply Nat.mod_lt_of_lt; assumption
  have x6_h_byte : x6_h.val < 256 := by rw [h_x6_h]; apply Nat.div_lt_of_lt; assumption
  have x7_l_byte : x7_l.val < 256 := by rw [h_x7_l]; apply Nat.mod_lt_of_lt; assumption
  have x7_h_byte : x7_h.val < 256 := by rw [h_x7_h]; apply Nat.div_lt_of_lt; assumption

  replace eq0 := byte_decomposition_lift x0_h_byte x1_l_byte two_power_byte eq0
  replace eq1 := byte_decomposition_lift x1_h_byte x2_l_byte two_power_byte eq1
  replace eq2 := byte_decomposition_lift x2_h_byte x3_l_byte two_power_byte eq2
  replace eq3 := byte_decomposition_lift x3_h_byte x4_l_byte two_power_byte eq3
  replace eq4 := byte_decomposition_lift x4_h_byte x5_l_byte two_power_byte eq4
  replace eq5 := byte_decomposition_lift x5_h_byte x6_l_byte two_power_byte eq5
  replace eq6 := byte_decomposition_lift x6_h_byte x7_l_byte two_power_byte eq6
  replace eq7 := byte_decomposition_lift x7_h_byte x0_l_byte two_power_byte eq7

  -- simplify the goal
  simp only [two_power_val, ZMod.val_natCast] at eq0 eq1 eq2 eq3 eq4 eq5 eq6 eq7
  rw [eq0, eq1, eq2, eq3, eq4, eq5, eq6, eq7]
  dsimp only

  have offset_mod_64 : offset.val % 64 = offset.val := by
    apply Nat.mod_eq_of_lt
    linarith [offset.is_lt]

  simp [h_x0_l, h_x0_h, h_x1_l, h_x1_h, h_x2_l, h_x2_h, h_x3_l, h_x3_h,
    h_x4_l, h_x4_h, h_x5_l, h_x5_h, h_x6_l, h_x6_h, h_x7_l, h_x7_h,
    offset_mod_64, -Nat.reducePow]

  rw [h_mod]
  -- if the offset is zero, then it is trivial: it is a special case since
  -- in that case the rotation is a no-op
  by_cases h_offset : offset.val = 0
  · rw [h_offset]
    simp only [Fin.isValue, Fin.val_zero, pow_zero, Nat.div_one, Nat.mod_one, tsub_zero,
      Nat.reducePow, Nat.mod_self, mul_zero, add_zero, zero_mul, zero_add, Nat.add_left_inj]
  · rw [two_off_eq_mod _ (by simp only [ne_eq, Fin.val_eq_zero_iff, Fin.isValue, h_offset,
      not_false_eq_true])]
    rw [h_div]
    -- proof technique: we care about only what happens to x0, all "internal" terms remain
    -- the same, and are just divided by 2^offset.val
    rw [shifted_decomposition_eq]
    repeat rw [shifted_decomposition_eq'' (by simp only [gt_iff_lt, Nat.ofNat_pos])]
    simp only [Nat.add_one_sub_one, pow_one, add_mul, add_assoc]

    -- we do a bit of expression juggling here
    rw [←add_assoc _ _ (_ * 256 ^ 7), soundness_simp]
    nth_rw 12 [←add_assoc]
    rw [soundness_simp]
    nth_rw 10 [←add_assoc]
    rw [soundness_simp]
    nth_rw 8 [←add_assoc]
    rw [soundness_simp]
    nth_rw 6 [←add_assoc]
    rw [soundness_simp]
    nth_rw 4 [←add_assoc]
    nth_rw 2 [Nat.mul_right_comm]
    rw [soundness_simp]
    nth_rw 2 [←add_assoc]
    rw [soundness_simp']
    nth_rw 7 [mul_assoc]

    -- at the end the terms are equal
    rw [h_x0_const]
    ac_rfl

end Gadgets.Rotation64.Theorems
