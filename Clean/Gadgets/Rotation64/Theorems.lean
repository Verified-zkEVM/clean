import Clean.Utils.Field
import Clean.Utils.Bitwise
import Clean.Types.U64
import Clean.Gadgets.ByteDecomposition.ByteDecomposition

variable {p : ℕ} [Fact p.Prime]
variable [p_large_enough: Fact (p > 2^16 + 2^8)]

namespace Gadgets.Rotation64.Theorems
open Bitwise (rot_right64)
open Gadgets.ByteDecomposition.Theorems (byte_decomposition_lift)

/--
We define a bit rotation on "byte vectors" like u64 by splitting each byte
into low and high bits, and moving the lowest low bits to the top and concatenating
each resulting (high, low) pair again.

The ultimate goal is to prove that this is equivalent to `rot_right64`.
-/
def rot_right64_bytes (o : ℕ) (_ : o < 8) (xs : Vector ℕ 8) : Vector ℕ 8 :=
  .ofFn fun ⟨ i, hi ⟩ =>
    (xs[(i + 1) % 8] % 2^o) * 2^(8-o) + xs[i] / 2^o

def rot_right8 (x : Fin 256) (offset : Fin 8) : Fin 256 :=
  let low := x % (2^offset.val)
  let high := x / (2^offset.val)
  low * (2^(8 - offset.val)) + high

def rot_left8 (x : Fin 256) (offset : Fin 8) : Fin 256 :=
  let low := x % (2^(8 - offset.val))
  let high := x / (2^(8 - offset.val))
  low * (2^offset.val) + high

lemma two_power_val {o : ℕ} (_ : o < 8) :
    ((2 ^ (8 - o) : ℕ) : F p).val = 2 ^ (8 - o) := by
  have : 2 ^ (8 - o) ≤ 2 ^ 8 := Nat.pow_le_pow_of_le (show 2 > 1 by norm_num) (by omega)
  rw [ZMod.val_natCast_of_lt]
  linarith [p_large_enough.elim]

lemma two_power_byte {o : ℕ} (ho : o < 8) :
    ZMod.val ((2 ^ (8 - o) : ℕ) : F p) ≤ 2^8 := by
  rw [two_power_val ho]
  exact Nat.pow_le_pow_of_le (show 2 > 1 by norm_num) (by omega)

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

lemma shifted_decomposition_eq {offset : ℕ} (ho : offset < 8) {x1 x2 : ℕ} :
    (x1 / 2 ^ offset + x2 % 2 ^ offset * 2 ^ (8 - offset)) * 256 =
    (2^offset * (x1 / 2^offset) + (x2 % 2^offset) * 256) * 2^(8 - offset) := by
  ring_nf
  simp only [Nat.add_left_inj]
  rw [Nat.mul_assoc, ←Nat.pow_add, Nat.add_sub_of_le (by linarith)]
  rfl

lemma shifted_decomposition_eq' {offset : ℕ} (ho : offset < 8) {x1 x2 i : ℕ} (hi : i > 0) :
    (x1 / 2 ^ offset + x2 % 2 ^ offset * 2 ^ (8 - offset)) * 256^i =
    (2^offset * (x1 / 2^offset) + (x2 % 2^offset) * 256) * 2^(8 - offset) * 256^(i-1) := by
  rw [Nat.pow_minus_one_mul hi, ←Nat.mul_assoc, shifted_decomposition_eq ho]

lemma shifted_decomposition_eq'' {offset : ℕ} (ho : offset < 8) {x1 x2 i : ℕ} (hi : i > 0) :
    (x1 / 2 ^ offset + x2 % 2 ^ offset * 2 ^ (8 - offset)) * 256^i =
    (2^offset * (x1 / 2^offset) * 2^(8 - offset) * 256^(i-1) +
    (x2 % 2^offset) * 2^(8 - offset) * 256^i) := by
  rw [shifted_decomposition_eq' ho hi]
  ring_nf
  rw [Nat.mul_assoc _ _ 256, Nat.mul_comm _ 256, Nat.pow_minus_one_mul hi]


lemma soundness_simp {offset : ℕ} {x y : ℕ} :
    x % 2 ^ offset * 2 ^ (8 - offset) * y + 2 ^ offset * (x / 2 ^ offset) * 2 ^ (8 - offset) * y =
    x * y * 2^ (8 - offset) := by
  rw [Nat.mul_assoc, Nat.mul_assoc, ←Nat.add_mul, add_comm, Nat.div_add_mod]
  ac_rfl

lemma soundness_simp' {offset : ℕ} {x : ℕ} :
    x % 2 ^ offset * 2 ^ (8 - offset) + 2 ^ offset * (x / 2 ^ offset) * 2 ^ (8 - offset) =
    x * 2^ (8 - offset) := by
  rw [←Nat.mul_one (x % 2 ^ offset * 2 ^ (8 - offset))]
  rw [←Nat.mul_one (2 ^ offset * (x / 2 ^ offset) * 2 ^ (8 - offset))]
  rw [soundness_simp, Nat.mul_one]

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

lemma h_x0_const {offset : ℕ} (ho : offset < 8) :
    2 ^ (8 - offset) * 256^7 = 2^(64 - offset) := by
  rw [show 256 = 2^8 by rfl, ←Nat.pow_mul, ←Nat.pow_add, add_comm]
  simp only [Nat.reduceMul, Nat.ofNat_pos, ne_eq, OfNat.ofNat_ne_one, not_false_eq_true,
    pow_right_inj₀]
  omega

theorem rotation64_bits_soundness (o : ℕ) (ho : o < 8) {
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
    (h_x0_l : x0_l.val = x0.val % 2^o)
    (h_x0_h : x0_h.val = x0.val / 2^o)
    (h_x1_l : x1_l.val = x1.val % 2^o)
    (h_x1_h : x1_h.val = x1.val / 2^o)
    (h_x2_l : x2_l.val = x2.val % 2^o)
    (h_x2_h : x2_h.val = x2.val / 2^o)
    (h_x3_l : x3_l.val = x3.val % 2^o)
    (h_x3_h : x3_h.val = x3.val / 2^o)
    (h_x4_l : x4_l.val = x4.val % 2^o)
    (h_x4_h : x4_h.val = x4.val / 2^o)
    (h_x5_l : x5_l.val = x5.val % 2^o)
    (h_x5_h : x5_h.val = x5.val / 2^o)
    (h_x6_l : x6_l.val = x6.val % 2^o)
    (h_x6_h : x6_h.val = x6.val / 2^o)
    (h_x7_l : x7_l.val = x7.val % 2^o)
    (h_x7_h : x7_h.val = x7.val / 2^o)
    (eq0 : y0 = x1_l * ↑(2 ^ (8 - o) : ℕ) + x0_h)
    (eq1 : y1 = x2_l * ↑(2 ^ (8 - o) : ℕ) + x1_h)
    (eq2 : y2 = x3_l * ↑(2 ^ (8 - o) : ℕ) + x2_h)
    (eq3 : y3 = x4_l * ↑(2 ^ (8 - o) : ℕ) + x3_h)
    (eq4 : y4 = x5_l * ↑(2 ^ (8 - o) : ℕ) + x4_h)
    (eq5 : y5 = x6_l * ↑(2 ^ (8 - o) : ℕ) + x5_h)
    (eq6 : y6 = x7_l * ↑(2 ^ (8 - o) : ℕ) + x6_h)
    (eq7 : y7 = x0_l * ↑(2 ^ (8 - o) : ℕ) + x7_h):
    let x_val := x0.val + x1.val * 256 + x2.val * 256 ^ 2 + x3.val * 256 ^ 3 + x4.val * 256 ^ 4 +
      x5.val * 256 ^ 5 + x6.val * 256 ^ 6 + x7.val * 256 ^ 7
    let y_val := y0.val + y1.val * 256 + y2.val * 256 ^ 2 + y3.val * 256 ^ 3 + y4.val * 256 ^ 4 +
      y5.val * 256 ^ 5 + y6.val * 256 ^ 6 + y7.val * 256 ^ 7
    y_val = (x_val) % 2 ^ (o % 64) * 2 ^ (64 - o % 64) + (x_val) / 2 ^ (o % 64) := by

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

  let two_power_byte := two_power_byte (p:=p) ho

  replace eq0 := byte_decomposition_lift x0_h_byte x1_l_byte two_power_byte eq0
  replace eq1 := byte_decomposition_lift x1_h_byte x2_l_byte two_power_byte eq1
  replace eq2 := byte_decomposition_lift x2_h_byte x3_l_byte two_power_byte eq2
  replace eq3 := byte_decomposition_lift x3_h_byte x4_l_byte two_power_byte eq3
  replace eq4 := byte_decomposition_lift x4_h_byte x5_l_byte two_power_byte eq4
  replace eq5 := byte_decomposition_lift x5_h_byte x6_l_byte two_power_byte eq5
  replace eq6 := byte_decomposition_lift x6_h_byte x7_l_byte two_power_byte eq6
  replace eq7 := byte_decomposition_lift x7_h_byte x0_l_byte two_power_byte eq7

  -- simplify the goal
  simp only [two_power_val ho, ZMod.val_natCast] at eq0 eq1 eq2 eq3 eq4 eq5 eq6 eq7
  rw [eq0, eq1, eq2, eq3, eq4, eq5, eq6, eq7]
  dsimp only

  have offset_mod_64 : o % 64 = o := by
    apply Nat.mod_eq_of_lt
    linarith

  simp [h_x0_l, h_x0_h, h_x1_l, h_x1_h, h_x2_l, h_x2_h, h_x3_l, h_x3_h,
    h_x4_l, h_x4_h, h_x5_l, h_x5_h, h_x6_l, h_x6_h, h_x7_l, h_x7_h,
    offset_mod_64, -Nat.reducePow]

  rw [h_mod (offset := ⟨o, ho⟩)]
  simp only
  -- if the offset is zero, then it is trivial: it is a special case since
  -- in that case the rotation is a no-op
  by_cases h_offset : o = 0
  · rw [h_offset]
    simp only [Fin.isValue, Fin.val_zero, pow_zero, Nat.div_one, Nat.mod_one, tsub_zero,
      Nat.reducePow, Nat.mod_self, mul_zero, add_zero, zero_mul, zero_add, Nat.add_left_inj]
  · rw [h_div (offset := ⟨o, ho⟩)]
    simp only
    -- proof technique: we care about only what happens to x0, all "internal" terms remain
    -- the same, and are just divided by 2^offset.val
    rw [shifted_decomposition_eq ho]
    repeat rw [shifted_decomposition_eq'' ho (by simp only [gt_iff_lt, Nat.ofNat_pos])]
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
    rw [h_x0_const ho]
    ac_rfl

end Gadgets.Rotation64.Theorems
