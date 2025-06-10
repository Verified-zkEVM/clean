import Clean.Utils.Field
import Clean.Utils.Bitwise
import Clean.Types.U64
import Clean.Gadgets.ByteDecomposition.ByteDecomposition

variable {p : ℕ} [Fact p.Prime]
variable [p_large_enough: Fact (p > 2^16 + 2^8)]

namespace Gadgets.Rotation64.Theorems
open Bitwise (rot_right64)
open Gadgets.ByteDecomposition.Theorems (byte_decomposition_lift)


def rot_right8 (x : Fin 256) (offset : Fin 8) : Fin 256 :=
  let low := x % (2^offset.val)
  let high := x / (2^offset.val)
  low * (2^(8 - offset.val)) + high

def rot_left8 (x : Fin 256) (offset : Fin 8) : Fin 256 :=
  let low := x % (2^(8 - offset.val))
  let high := x / (2^(8 - offset.val))
  low * (2^offset.val) + high


lemma two_power_val {offset : Fin 8} :
    ((2 ^ (8 - offset.val) % 256 : ℕ) : F p).val = 2 ^ (8 - offset.val) % 256 := by
  rw [ZMod.val_natCast]
  apply Nat.mod_eq_of_lt
  have h : 2 ^ (8 - offset.val) % 256 < 256 := by apply Nat.mod_lt; linarith
  linarith [h, p_large_enough.elim]

lemma mul_mod_256_off (offset : Fin 8) (x i : ℕ) (h : i > 0):
    (x * 256^i) % 2^offset.val = 0 := by
  rw [Nat.mul_mod, Nat.pow_mod]
  fin_cases offset <;>
  simp only [Nat.reducePow, Nat.reduceMod, Nat.zero_pow h, Nat.zero_mod, mul_zero]

lemma Nat.pow_minus_one_mul {x y : ℕ} (hy : y > 0) : x ^ y = x * x ^ (y - 1) := by
  nth_rw 2 [←Nat.pow_one x]
  rw [←Nat.pow_add, Nat.add_sub_of_le (by linarith [hy])]

lemma divides_256_two_power {offset : Fin 8} {x i : ℕ} (h : i > 0):
    (2^offset.val) ∣ x * (256 ^ i) := by
  rw [show 256 = 2^8 by rfl, ←Nat.pow_mul]
  apply Nat.dvd_mul_left_of_dvd
  apply Nat.pow_dvd_pow
  linarith [offset.is_lt]

lemma div_256_two_power {offset : Fin 8} {i : ℕ} (h : i > 0):
    256^i / 2^offset.val = 256^(i-1) * 2^(8 - offset.val) := by
  rw [show 256 = 2^8 by rfl, ←Nat.pow_mul, Nat.pow_div]
  rw [←Nat.pow_mul, ←Nat.pow_add]
  rw [Nat.mul_sub_left_distrib, Nat.mul_one]
  rw [Nat.sub_add_sub_cancel]
  repeat linarith [offset.is_lt]

lemma mul_div_256_off {offset : Fin 8} {x : ℕ} (i : ℕ) (h : i > 0):
    (x * 256^i) / 2^offset.val = x * 256^(i-1) * 2^(8 - offset.val) := by
  rw [Nat.mul_div_assoc, div_256_two_power h]
  rw [show 256=2^8 by rfl, ←Nat.pow_mul]
  ac_rfl
  rw [show 256=2^8 by rfl, ←Nat.pow_mul]
  apply Nat.pow_dvd_pow
  linarith [offset.is_lt]


lemma two_off_eq_mod (offset : Fin 8) (h : offset.val ≠ 0):
    (2 ^ (8 - offset.val) % 256) = 2 ^ (8 - offset.val) := by
  apply Nat.mod_eq_of_lt
  fin_cases offset <;>
    first
    | contradiction
    | simp


lemma shifted_decomposition_eq {offset : Fin 8} {x1 x2 : ℕ} :
    (x1 / 2 ^ offset.val + x2 % 2 ^ offset.val * 2 ^ (8 - offset.val)) * 256 =
    (2^offset.val * (x1 / 2^offset.val) + (x2 % 2^offset.val) * 256) * 2^(8 - offset.val) := by
  ring_nf
  simp only [Nat.add_left_inj]
  rw [Nat.mul_assoc, ←Nat.pow_add, Nat.add_sub_of_le (by linarith [offset.is_lt])]
  rfl

lemma shifted_decomposition_eq' {offset : Fin 8} {x1 x2 i : ℕ} (hi : i > 0) :
    (x1 / 2 ^ offset.val + x2 % 2 ^ offset.val * 2 ^ (8 - offset.val)) * 256^i =
    (2^offset.val * (x1 / 2^offset.val) + (x2 % 2^offset.val) * 256) * 2^(8 - offset.val) * 256^(i-1) := by
  rw [Nat.pow_minus_one_mul hi, ←Nat.mul_assoc, shifted_decomposition_eq]

lemma shifted_decomposition_eq'' {offset : Fin 8} {x1 x2 i : ℕ} (hi : i > 0) :
    (x1 / 2 ^ offset.val + x2 % 2 ^ offset.val * 2 ^ (8 - offset.val)) * 256^i =
    (2^offset.val * (x1 / 2^offset.val) * 2^(8 - offset.val) * 256^(i-1) +
    (x2 % 2^offset.val) * 2^(8 - offset.val) * 256^i) := by
  rw [shifted_decomposition_eq' hi]
  ring_nf
  rw [Nat.mul_assoc _ _ 256, Nat.mul_comm _ 256, Nat.pow_minus_one_mul hi]


lemma soundness_simp {offset : Fin 8} {x y : ℕ} :
    x % 2 ^ offset.val * 2 ^ (8 - offset.val) * y + 2 ^ offset.val * (x / 2 ^ offset.val) * 2 ^ (8 - offset.val) * y =
    x * y * 2^ (8 - offset.val) := by
  rw [Nat.mul_assoc, Nat.mul_assoc, ←Nat.add_mul, add_comm, Nat.div_add_mod]
  ac_rfl

lemma soundness_simp' {offset : Fin 8} {x : ℕ} :
    x % 2 ^ offset.val * 2 ^ (8 - offset.val) + 2 ^ offset.val * (x / 2 ^ offset.val) * 2 ^ (8 - offset.val) =
    x * 2^ (8 - offset.val) := by
  rw [←Nat.mul_one (x % 2 ^ offset.val * 2 ^ (8 - offset.val))]
  rw [←Nat.mul_one (2 ^ offset.val * (x / 2 ^ offset.val) * 2 ^ (8 - offset.val))]
  rw [soundness_simp, Nat.mul_one]

omit p_large_enough in
lemma two_power_byte {offset : Fin 8} :
    ZMod.val ((2 ^ (8 - offset.val) % 256 : ℕ) : F p) < 256 := by
  rw [ZMod.val_natCast]
  apply Nat.mod_lt_of_lt
  apply Nat.mod_lt
  linarith

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


omit [Fact (Nat.Prime p)] p_large_enough in
lemma soundnessCase1 (x0 x1 x2 x3 x4 x5 x6 x7 : F p) (as : ZMod.val x0 < 256 ∧ ZMod.val x1 < 256 ∧ ZMod.val x2 < 256 ∧ ZMod.val x3 < 256 ∧ ZMod.val x4 < 256 ∧ ZMod.val x5 < 256 ∧ ZMod.val x6 < 256 ∧ ZMod.val x7 < 256) : { x0 := x1, x1 := x2, x2 := x3, x3 := x4, x4 := x5, x5 := x6, x6 := x7, x7 := x0 : U64 _}.value =
  rot_right64 { x0 := x0, x1 := x1, x2 := x2, x3 := x3, x4 := x4, x5 := x5, x6 := x6, x7 := x7 : U64 _}.value 8 := by
  simp only [U64.value, rot_right64]
  rw [
    show (8 % 64) = 8 by norm_num,
    show (64 - 8) = 56 by norm_num,
  ]
  have x0_pos : 0 ≤ x0.val := by exact Nat.zero_le _
  zify at *
  set x0 : ℤ := x0.val.cast
  set x1 : ℤ := x1.val.cast
  set x2 : ℤ := x2.val.cast
  set x3 : ℤ := x3.val.cast
  set x4 : ℤ := x4.val.cast
  set x5 : ℤ := x5.val.cast
  set x6 : ℤ := x6.val.cast
  set x7 : ℤ := x7.val.cast

  have powers_mod :
    (72057594037927936 : ℤ) % 256 = 0 ∧
    (281474976710656 : ℤ) % 256 = 0 ∧
    (1099511627776 : ℤ) % 256 = 0 ∧
    (4294967296 : ℤ) % 256 = 0 ∧
    (16777216 : ℤ) % 256 = 0 ∧
    (65536 : ℤ) % 256 = 0 := by norm_num


  have h : (x0 + x1 * 256 + x2 * 256 ^ 2 + x3 * 256 ^ 3 + x4 * 256 ^ 4 + x5 * 256 ^ 5 + x6 * 256 ^ 6 + x7 * 256 ^ 7) % 2 ^ 8 = x0 := by
    repeat
      ring_nf
      rw [Int.add_emod, Int.mul_emod]
      simp only [powers_mod]
      norm_num
    rw [Int.emod_eq_of_lt x0_pos (by linarith)]


  have h' : (x0 + x1 * 256 + x2 * 256 ^ 2 + x3 * 256 ^ 3 + x4 * 256 ^ 4 + x5 * 256 ^ 5 + x6 * 256 ^ 6 + x7 * 256 ^ 7) / 2 ^ 8 =
      x1 + x2 * 256 + x3 * 256 ^ 2 + x4 * 256 ^ 3 + x5 * 256 ^ 4 + x6 * 256 ^ 5 + x7 * 256 ^ 6 := by

    repeat
      ring_nf
      rw [Int.add_ediv_of_dvd_right (by
        rw [Int.dvd_iff_emod_eq_zero, Int.mul_emod]
        try rw [show ((72057594037927936 : ℤ) % 256) = 0 by rfl]
        try rw [show ((281474976710656 : ℤ) % 256) = 0 by rfl]
        try rw [show ((1099511627776 : ℤ) % 256) = 0 by rfl]
        try rw [show ((4294967296 : ℤ) % 256) = 0 by rfl]
        try rw [show ((16777216 : ℤ) % 256) = 0 by rfl]
        try rw [show ((65536 : ℤ) % 256) = 0 by rfl]
        rfl)]
      rw [Int.mul_ediv_assoc _ (by norm_num)]
      norm_num
    rw [Int.ediv_eq_zero_of_lt (by simp only [x0_pos]) (by simp only [as])]

  rw [h, h']
  ring

omit [Fact (Nat.Prime p)] p_large_enough in
lemma soundnessCase2 (x0 x1 x2 x3 x4 x5 x6 x7 : F p) (as : ZMod.val x0 < 256 ∧ ZMod.val x1 < 256 ∧ ZMod.val x2 < 256 ∧ ZMod.val x3 < 256 ∧ ZMod.val x4 < 256 ∧ ZMod.val x5 < 256 ∧ ZMod.val x6 < 256 ∧ ZMod.val x7 < 256) : { x0 := x2, x1 := x3, x2 := x4, x3 := x5, x4 := x6, x5 := x7, x6 := x0, x7 := x1 : U64 _}.value =
  rot_right64 { x0 := x0, x1 := x1, x2 := x2, x3 := x3, x4 := x4, x5 := x5, x6 := x6, x7 := x7 : U64 _}.value 16 := by
  simp only [U64.value, rot_right64]
  rw [
    show (16 % 64) = 16 by norm_num,
    show (64 - 16) = 48 by norm_num,
  ]
  have x0_pos : 0 ≤ x0.val := by exact Nat.zero_le _
  have x1_pos : 0 ≤ x1.val := by exact Nat.zero_le _
  have x0_x1_pos : 0 ≤ x0.val + x1.val * 256 := by
    exact Nat.le_add_right_of_le x0_pos
  zify at *
  set x0 : ℤ := x0.val.cast
  set x1 : ℤ := x1.val.cast
  set x2 : ℤ := x2.val.cast
  set x3 : ℤ := x3.val.cast
  set x4 : ℤ := x4.val.cast
  set x5 : ℤ := x5.val.cast
  set x6 : ℤ := x6.val.cast
  set x7 : ℤ := x7.val.cast


  have powers_mod :
    (72057594037927936 : ℤ) % 65536 = 0 ∧
    (281474976710656 : ℤ) % 65536 = 0 ∧
    (1099511627776 : ℤ) % 65536 = 0 ∧
    (4294967296 : ℤ) % 65536 = 0 ∧
    (16777216 : ℤ) % 65536 = 0 := by norm_num

  have h : (x0 + x1 * 256 + x2 * 256 ^ 2 + x3 * 256 ^ 3 + x4 * 256 ^ 4 + x5 * 256 ^ 5 + x6 * 256 ^ 6 + x7 * 256 ^ 7) % 2 ^ 16 = x0 + x1 * 256 := by

    norm_num
    repeat
      rw [Int.add_emod, Int.mul_emod]
      simp only [powers_mod]
      norm_num
    rw [Int.emod_eq_of_lt x0_x1_pos (by linarith)]

  have h' : (x0 + x1 * 256 + x2 * 256 ^ 2 + x3 * 256 ^ 3 + x4 * 256 ^ 4 + x5 * 256 ^ 5 + x6 * 256 ^ 6 + x7 * 256 ^ 7) / 2 ^ 16 =
      x2 + x3 * 256 + x4 * 256 ^ 2 + x5 * 256 ^ 3 + x6 * 256 ^ 4 + x7 * 256 ^ 5 := by

    repeat
      norm_num
      rw [Int.add_ediv_of_dvd_right (by
        rw [Int.dvd_iff_emod_eq_zero, Int.mul_emod]
        try rw [show ((72057594037927936 : ℤ) % 65536) = 0 by rfl]
        try rw [show ((281474976710656 : ℤ) % 65536) = 0 by rfl]
        try rw [show ((1099511627776 : ℤ) % 65536) = 0 by rfl]
        try rw [show ((4294967296 : ℤ) % 65536) = 0 by rfl]
        try rw [show ((16777216 : ℤ) % 65536) = 0 by rfl]
        rfl)]
      rw [Int.mul_ediv_assoc _ (by norm_num)]
      norm_num
    rw [Int.ediv_eq_zero_of_lt (by simp only [x0_x1_pos]) (by linarith)]

  rw [h, h']
  ring

omit [Fact (Nat.Prime p)] p_large_enough in
lemma soundnessCase3 (x0 x1 x2 x3 x4 x5 x6 x7 : F p) (as : ZMod.val x0 < 256 ∧ ZMod.val x1 < 256 ∧ ZMod.val x2 < 256 ∧ ZMod.val x3 < 256 ∧ ZMod.val x4 < 256 ∧ ZMod.val x5 < 256 ∧ ZMod.val x6 < 256 ∧ ZMod.val x7 < 256) : { x0 := x3, x1 := x4, x2 := x5, x3 := x6, x4 := x7, x5 := x0, x6 := x1, x7 := x2 : U64 _}.value =
  rot_right64 { x0 := x0, x1 := x1, x2 := x2, x3 := x3, x4 := x4, x5 := x5, x6 := x6, x7 := x7 : U64 _}.value 24 := by
  simp only [U64.value, rot_right64]
  rw [
    show (24 % 64) = 24 by norm_num,
    show (64 - 24) = 40 by norm_num,
  ]
  have x0_pos : 0 ≤ x0.val := by exact Nat.zero_le _
  have x1_pos : 0 ≤ x1.val := by exact Nat.zero_le _
  have x2_pos : 0 ≤ x2.val := by exact Nat.zero_le _
  have x0_x1_pos : 0 ≤ x0.val + x1.val * 256 := by
    exact Nat.le_add_right_of_le x0_pos
  have x0_x1_x2_pos : 0 ≤ x0.val + x1.val * 256 + x2.val * 65536 := by
    exact Nat.le_add_right_of_le x0_x1_pos
  zify at *
  set x0 : ℤ := x0.val.cast
  set x1 : ℤ := x1.val.cast
  set x2 : ℤ := x2.val.cast
  set x3 : ℤ := x3.val.cast
  set x4 : ℤ := x4.val.cast
  set x5 : ℤ := x5.val.cast
  set x6 : ℤ := x6.val.cast
  set x7 : ℤ := x7.val.cast

  have powers_mod :
    (72057594037927936 : ℤ) % 16777216 = 0 ∧
    (281474976710656 : ℤ) % 16777216 = 0 ∧
    (1099511627776 : ℤ) % 16777216 = 0 ∧
    (4294967296 : ℤ) % 16777216 = 0 := by norm_num

  have h : (x0 + x1 * 256 + x2 * 256 ^ 2 + x3 * 256 ^ 3 + x4 * 256 ^ 4 + x5 * 256 ^ 5 + x6 * 256 ^ 6 + x7 * 256 ^ 7) % 2 ^ 24 = x0 + x1 * 256 + x2 * 256 ^ 2 := by
    repeat
      norm_num
      rw [Int.add_emod, Int.mul_emod]
      simp only [powers_mod]
      norm_num
    rw [Int.emod_eq_of_lt x0_x1_x2_pos (by linarith)]

  have h' : (x0 + x1 * 256 + x2 * 256 ^ 2 + x3 * 256 ^ 3 + x4 * 256 ^ 4 + x5 * 256 ^ 5 + x6 * 256 ^ 6 + x7 * 256 ^ 7) / 2 ^ 24 =
      x3 + x4 * 256 + x5 * 256 ^ 2 + x6 * 256 ^ 3 + x7 * 256 ^ 4 := by
    repeat
      norm_num
      rw [Int.add_ediv_of_dvd_right (by
        rw [Int.dvd_iff_emod_eq_zero, Int.mul_emod]
        try rw [show ((72057594037927936 : ℤ) % 16777216) = 0 by rfl]
        try rw [show ((281474976710656 : ℤ) % 16777216) = 0 by rfl]
        try rw [show ((1099511627776 : ℤ) % 16777216) = 0 by rfl]
        try rw [show ((4294967296 : ℤ) % 16777216) = 0 by rfl]
        rfl)]
      rw [Int.mul_ediv_assoc _ (by norm_num)]
      norm_num
    rw [Int.ediv_eq_zero_of_lt (by simp only [x0_x1_x2_pos]) (by linarith)]

  rw [h, h']
  ring

omit [Fact (Nat.Prime p)] p_large_enough in
lemma soundnessCase4 (x0 x1 x2 x3 x4 x5 x6 x7 : F p) (as : ZMod.val x0 < 256 ∧ ZMod.val x1 < 256 ∧ ZMod.val x2 < 256 ∧ ZMod.val x3 < 256 ∧ ZMod.val x4 < 256 ∧ ZMod.val x5 < 256 ∧ ZMod.val x6 < 256 ∧ ZMod.val x7 < 256) : { x0 := x4, x1 := x5, x2 := x6, x3 := x7, x4 := x0, x5 := x1, x6 := x2, x7 := x3 : U64 _}.value = rot_right64 { x0 := x0, x1 := x1, x2 := x2, x3 := x3, x4 := x4, x5 := x5, x6 := x6, x7 := x7 : U64 _}.value 32 := by
  simp only [U64.value, rot_right64]
  rw [
    show (32 % 64) = 32 by norm_num,
    show (64 - 32) = 32 by norm_num,
  ]
  have x0_pos : 0 ≤ x0.val := by exact Nat.zero_le _
  have x1_pos : 0 ≤ x1.val := by exact Nat.zero_le _
  have x2_pos : 0 ≤ x2.val := by exact Nat.zero_le _
  have x3_pos : 0 ≤ x3.val := by exact Nat.zero_le _
  have x0_x1_pos : 0 ≤ x0.val + x1.val * 256 := by
    exact Nat.le_add_right_of_le x0_pos
  have x0_x1_x2_pos : 0 ≤ x0.val + x1.val * 256 + x2.val * 65536 := by
    exact Nat.le_add_right_of_le x0_x1_pos
  have x0_x1_x2_x3_pos : 0 ≤ x0.val + x1.val * 256 + x2.val * 65536 + x3.val * 16777216 := by
    exact Nat.le_add_right_of_le x0_x1_x2_pos
  zify at *
  set x0 : ℤ := x0.val.cast
  set x1 : ℤ := x1.val.cast
  set x2 : ℤ := x2.val.cast
  set x3 : ℤ := x3.val.cast
  set x4 : ℤ := x4.val.cast
  set x5 : ℤ := x5.val.cast
  set x6 : ℤ := x6.val.cast
  set x7 : ℤ := x7.val.cast

  have powers_mod :
    (72057594037927936 : ℤ) % 4294967296 = 0 ∧
    (281474976710656 : ℤ) % 4294967296 = 0 ∧
    (1099511627776 : ℤ) % 4294967296 = 0 := by norm_num

  have h : (x0 + x1 * 256 + x2 * 256 ^ 2 + x3 * 256 ^ 3 + x4 * 256 ^ 4 + x5 * 256 ^ 5 + x6 * 256 ^ 6 + x7 * 256 ^ 7) % 2 ^ 32 = x0 + x1 * 256 + x2 * 256 ^ 2 + x3 * 256 ^ 3 := by
    norm_num
    repeat
      rw [Int.add_emod, Int.mul_emod]
      simp only [powers_mod]
      norm_num

    rw [Int.emod_eq_of_lt x0_x1_x2_x3_pos (by linarith)]

  have h' : (x0 + x1 * 256 + x2 * 256 ^ 2 + x3 * 256 ^ 3 + x4 * 256 ^ 4 + x5 * 256 ^ 5 + x6 * 256 ^ 6 + x7 * 256 ^ 7) / 2 ^ 32 =
      x4 + x5 * 256 + x6 * 256 ^ 2 + x7 * 256 ^ 3 := by
    repeat
      norm_num
      rw [Int.add_ediv_of_dvd_right (by
        rw [Int.dvd_iff_emod_eq_zero, Int.mul_emod]
        try rw [show ((72057594037927936 : ℤ) % 4294967296) = 0 by rfl]
        try rw [show ((281474976710656 : ℤ) % 4294967296) = 0 by rfl]
        try rw [show ((1099511627776 : ℤ) % 4294967296) = 0 by rfl]
        rfl)]
      rw [Int.mul_ediv_assoc _ (by norm_num)]
      norm_num
    rw [Int.ediv_eq_zero_of_lt (by simp only [x0_x1_x2_x3_pos]) (by linarith)]

  rw [h, h']
  ring

omit [Fact (Nat.Prime p)] p_large_enough in
lemma soundnessCase5 (x0 x1 x2 x3 x4 x5 x6 x7 : F p) (as : ZMod.val x0 < 256 ∧ ZMod.val x1 < 256 ∧ ZMod.val x2 < 256 ∧ ZMod.val x3 < 256 ∧ ZMod.val x4 < 256 ∧ ZMod.val x5 < 256 ∧ ZMod.val x6 < 256 ∧ ZMod.val x7 < 256) : { x0 := x5, x1 := x6, x2 := x7, x3 := x0, x4 := x1, x5 := x2, x6 := x3, x7 := x4 : U64 _}.value = rot_right64 { x0 := x0, x1 := x1, x2 := x2, x3 := x3, x4 := x4, x5 := x5, x6 := x6, x7 := x7 : U64 _}.value 40 := by
  simp only [U64.value, rot_right64]
  rw [
    show (40 % 64) = 40 by norm_num,
    show (64 - 40) = 24 by norm_num,
  ]
  have x0_pos : 0 ≤ x0.val := by exact Nat.zero_le _
  have x1_pos : 0 ≤ x1.val := by exact Nat.zero_le _
  have x2_pos : 0 ≤ x2.val := by exact Nat.zero_le _
  have x3_pos : 0 ≤ x3.val := by exact Nat.zero_le _
  have x4_pos : 0 ≤ x4.val := by exact Nat.zero_le _
  have x0_x1_pos : 0 ≤ x0.val + x1.val * 256 := by
    exact Nat.le_add_right_of_le x0_pos
  have x0_x1_x2_pos : 0 ≤ x0.val + x1.val * 256 + x2.val * 65536 := by
    exact Nat.le_add_right_of_le x0_x1_pos
  have x0_x1_x2_x3_pos : 0 ≤ x0.val + x1.val * 256 + x2.val * 65536 + x3.val * 16777216 := by
    exact Nat.le_add_right_of_le x0_x1_x2_pos
  have x0_x1_x2_x3_x4_pos : 0 ≤ x0.val + x1.val * 256 + x2.val * 65536 + x3.val * 16777216 + x4.val * 4294967296 := by
    exact Nat.le_add_right_of_le x0_x1_x2_x3_pos
  zify at *
  set x0 : ℤ := x0.val.cast
  set x1 : ℤ := x1.val.cast
  set x2 : ℤ := x2.val.cast
  set x3 : ℤ := x3.val.cast
  set x4 : ℤ := x4.val.cast
  set x5 : ℤ := x5.val.cast
  set x6 : ℤ := x6.val.cast
  set x7 : ℤ := x7.val.cast

  have powers_mod :
    (72057594037927936 : ℤ) % 1099511627776 = 0 ∧
    (281474976710656 : ℤ) % 1099511627776 = 0 := by norm_num

  have h : (x0 + x1 * 256 + x2 * 256 ^ 2 + x3 * 256 ^ 3 + x4 * 256 ^ 4 + x5 * 256 ^ 5 + x6 * 256 ^ 6 + x7 * 256 ^ 7) % 2 ^ 40 = x0 + x1 * 256 + x2 * 256 ^ 2 + x3 * 256 ^ 3 + x4 * 256 ^ 4 := by
    repeat
      norm_num
      rw [Int.add_emod, Int.mul_emod]
      simp only [powers_mod]
      norm_num

    rw [Int.emod_eq_of_lt x0_x1_x2_x3_x4_pos (by linarith)]

  have h' : (x0 + x1 * 256 + x2 * 256 ^ 2 + x3 * 256 ^ 3 + x4 * 256 ^ 4 + x5 * 256 ^ 5 + x6 * 256 ^ 6 + x7 * 256 ^ 7) / 2 ^ 40 =
      x5 + x6 * 256 + x7 * 256 ^ 2 := by
    repeat
      norm_num
      rw [Int.add_ediv_of_dvd_right (by
        rw [Int.dvd_iff_emod_eq_zero, Int.mul_emod]
        try rw [show ((72057594037927936 : ℤ) % 1099511627776) = 0 by rfl]
        try rw [show ((281474976710656 : ℤ) % 1099511627776) = 0 by rfl]
        rfl)]
      rw [Int.mul_ediv_assoc _ (by norm_num)]
      norm_num
    rw [Int.ediv_eq_zero_of_lt (by simp only [x0_x1_x2_x3_x4_pos]) (by linarith)]

  rw [h, h']
  ring

omit [Fact (Nat.Prime p)] p_large_enough in
lemma soundnessCase6 (x0 x1 x2 x3 x4 x5 x6 x7 : F p) (as : ZMod.val x0 < 256 ∧ ZMod.val x1 < 256 ∧ ZMod.val x2 < 256 ∧ ZMod.val x3 < 256 ∧ ZMod.val x4 < 256 ∧ ZMod.val x5 < 256 ∧ ZMod.val x6 < 256 ∧ ZMod.val x7 < 256) : { x0 := x6, x1 := x7, x2 := x0, x3 := x1, x4 := x2, x5 := x3, x6 := x4, x7 := x5 : U64 _}.value = rot_right64 { x0 := x0, x1 := x1, x2 := x2, x3 := x3, x4 := x4, x5 := x5, x6 := x6, x7 := x7 : U64 _}.value 48 := by
  simp only [U64.value, rot_right64]
  rw [
    show (48 % 64) = 48 by norm_num,
    show (64 - 48) = 16 by norm_num,
  ]
  have x0_pos : 0 ≤ x0.val := by exact Nat.zero_le _
  have x1_pos : 0 ≤ x1.val := by exact Nat.zero_le _
  have x2_pos : 0 ≤ x2.val := by exact Nat.zero_le _
  have x3_pos : 0 ≤ x3.val := by exact Nat.zero_le _
  have x4_pos : 0 ≤ x4.val := by exact Nat.zero_le _
  have x5_pos : 0 ≤ x5.val := by exact Nat.zero_le _
  have x0_x1_pos : 0 ≤ x0.val + x1.val * 256 := by
    exact Nat.le_add_right_of_le x0_pos
  have x0_x1_x2_pos : 0 ≤ x0.val + x1.val * 256 + x2.val * 65536 := by
    exact Nat.le_add_right_of_le x0_x1_pos
  have x0_x1_x2_x3_pos : 0 ≤ x0.val + x1.val * 256 + x2.val * 65536 + x3.val * 16777216 := by
    exact Nat.le_add_right_of_le x0_x1_x2_pos
  have x0_x1_x2_x3_x4_pos : 0 ≤ x0.val + x1.val * 256 + x2.val * 65536 + x3.val * 16777216 + x4.val * 4294967296 := by
    exact Nat.le_add_right_of_le x0_x1_x2_x3_pos
  have x0_x1_x2_x3_x4_x5_pos : 0 ≤ x0.val + x1.val * 256 + x2.val * 65536 + x3.val * 16777216 + x4.val * 4294967296 + x5.val * 1099511627776 := by
    exact Nat.le_add_right_of_le x0_x1_x2_x3_x4_pos
  zify at *
  set x0 : ℤ := x0.val.cast
  set x1 : ℤ := x1.val.cast
  set x2 : ℤ := x2.val.cast
  set x3 : ℤ := x3.val.cast
  set x4 : ℤ := x4.val.cast
  set x5 : ℤ := x5.val.cast
  set x6 : ℤ := x6.val.cast
  set x7 : ℤ := x7.val.cast

  have powers_mod :
    (72057594037927936 : ℤ) % 281474976710656 = 0 := by norm_num

  have h : (x0 + x1 * 256 + x2 * 256 ^ 2 + x3 * 256 ^ 3 + x4 * 256 ^ 4 + x5 * 256 ^ 5 + x6 * 256 ^ 6 + x7 * 256 ^ 7) % 2 ^ 48 = x0 + x1 * 256 + x2 * 256 ^ 2 + x3 * 256 ^ 3 + x4 * 256 ^ 4 + x5 * 256 ^ 5 := by
    repeat
      norm_num
      rw [Int.add_emod, Int.mul_emod]
      rw [show ((72057594037927936 : ℤ) % 281474976710656) = 0 by rfl]
      norm_num
    rw [Int.emod_eq_of_lt x0_x1_x2_x3_x4_x5_pos (by linarith)]

  have h' : (x0 + x1 * 256 + x2 * 256 ^ 2 + x3 * 256 ^ 3 + x4 * 256 ^ 4 + x5 * 256 ^ 5 + x6 * 256 ^ 6 + x7 * 256 ^ 7) / 2 ^ 48 =
      x6 + x7 * 256 := by
    repeat
      norm_num
      rw [Int.add_ediv_of_dvd_right (by
        rw [Int.dvd_iff_emod_eq_zero, Int.mul_emod]
        try rw [show ((72057594037927936 : ℤ) % 281474976710656) = 0 by rfl]
        rfl)]
      rw [Int.mul_ediv_assoc _ (by norm_num)]
      norm_num
    rw [Int.ediv_eq_zero_of_lt (by simp only [x0_x1_x2_x3_x4_x5_pos]) (by linarith)]

  rw [h, h']
  ring

omit [Fact (Nat.Prime p)] p_large_enough in
lemma soundnessCase7 (x0 x1 x2 x3 x4 x5 x6 x7 : F p) (as : ZMod.val x0 < 256 ∧ ZMod.val x1 < 256 ∧ ZMod.val x2 < 256 ∧ ZMod.val x3 < 256 ∧ ZMod.val x4 < 256 ∧ ZMod.val x5 < 256 ∧ ZMod.val x6 < 256 ∧ ZMod.val x7 < 256) : { x0 := x7, x1 := x0, x2 := x1, x3 := x2, x4 := x3, x5 := x4, x6 := x5, x7 := x6 : U64 _}.value = rot_right64 { x0 := x0, x1 := x1, x2 := x2, x3 := x3, x4 := x4, x5 := x5, x6 := x6, x7 := x7 : U64 _}.value 56 := by
  simp only [U64.value, rot_right64]
  rw [
    show (56 % 64) = 56 by norm_num,
    show (64 - 56) = 8 by norm_num,
  ]
  have x0_pos : 0 ≤ x0.val := by exact Nat.zero_le _
  have x1_pos : 0 ≤ x1.val := by exact Nat.zero_le _
  have x2_pos : 0 ≤ x2.val := by exact Nat.zero_le _
  have x3_pos : 0 ≤ x3.val := by exact Nat.zero_le _
  have x4_pos : 0 ≤ x4.val := by exact Nat.zero_le _
  have x5_pos : 0 ≤ x5.val := by exact Nat.zero_le _
  have x6_pos : 0 ≤ x6.val := by exact Nat.zero_le _
  have x0_x1_pos : 0 ≤ x0.val + x1.val * 256 := by
    exact Nat.le_add_right_of_le x0_pos
  have x0_x1_x2_pos : 0 ≤ x0.val + x1.val * 256 + x2.val * 65536 := by
    exact Nat.le_add_right_of_le x0_x1_pos
  have x0_x1_x2_x3_pos : 0 ≤ x0.val + x1.val * 256 + x2.val * 65536 + x3.val * 16777216 := by
    exact Nat.le_add_right_of_le x0_x1_x2_pos
  have x0_x1_x2_x3_x4_pos : 0 ≤ x0.val + x1.val * 256 + x2.val * 65536 + x3.val * 16777216 + x4.val * 4294967296 := by
    exact Nat.le_add_right_of_le x0_x1_x2_x3_pos
  have x0_x1_x2_x3_x4_x5_pos : 0 ≤ x0.val + x1.val * 256 + x2.val * 65536 + x3.val * 16777216 + x4.val * 4294967296 + x5.val * 1099511627776 := by
    exact Nat.le_add_right_of_le x0_x1_x2_x3_x4_pos
  have x0_x1_x2_x3_x4_x5_x6_pos : 0 ≤ x0.val + x1.val * 256 + x2.val * 65536 + x3.val * 16777216 + x4.val * 4294967296 + x5.val * 1099511627776 + x6.val * 281474976710656 := by
    exact Nat.le_add_right_of_le x0_x1_x2_x3_x4_x5_pos
  zify at *
  set x0 : ℤ := x0.val.cast
  set x1 : ℤ := x1.val.cast
  set x2 : ℤ := x2.val.cast
  set x3 : ℤ := x3.val.cast
  set x4 : ℤ := x4.val.cast
  set x5 : ℤ := x5.val.cast
  set x6 : ℤ := x6.val.cast
  set x7 : ℤ := x7.val.cast

  have h : (x0 + x1 * 256 + x2 * 256 ^ 2 + x3 * 256 ^ 3 + x4 * 256 ^ 4 + x5 * 256 ^ 5 + x6 * 256 ^ 6 + x7 * 256 ^ 7) % 2 ^ 56 = x0 + x1 * 256 + x2 * 256 ^ 2 + x3 * 256 ^ 3 + x4 * 256 ^ 4 + x5 * 256 ^ 5 + x6 * 256 ^ 6 := by
    norm_num
    rw [Int.add_emod, Int.mul_emod]
    norm_num
    rw [Int.emod_eq_of_lt x6_pos (by linarith)]
    rw [Int.emod_eq_of_lt x0_x1_x2_x3_x4_x5_x6_pos (by linarith)]

  have h' : (x0 + x1 * 256 + x2 * 256 ^ 2 + x3 * 256 ^ 3 + x4 * 256 ^ 4 + x5 * 256 ^ 5 + x6 * 256 ^ 6 + x7 * 256 ^ 7) / 2 ^ 56 = x7 := by
    repeat
      norm_num
      rw [Int.add_ediv_of_dvd_right (by
        rw [Int.dvd_iff_emod_eq_zero, Int.mul_emod]
        rfl)]
      rw [Int.mul_ediv_assoc _ (by norm_num)]
      norm_num
    rw [Int.ediv_eq_zero_of_lt (by simp only [x0_x1_x2_x3_x4_x5_x6_pos]) (by linarith)]

  rw [h, h']
  ring



end Gadgets.Rotation64.Theorems
