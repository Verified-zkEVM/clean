import Clean.Utils.Field
import Clean.Utils.Bitwise
import Clean.Utils.Rotation
import Clean.Types.U64

variable {p : ℕ} [Fact p.Prime]
variable [p_large_enough: Fact (p > 2^16 + 2^8)]

namespace Gadgets.Rotation64.Theorems
open Bitwise (rot_right64)
open Utils.Rotation

/--
We define a bit rotation on "byte vectors" like u64 by splitting each byte
into low and high bits, and moving the lowest low bits to the top and concatenating
each resulting (high, low) pair again.

The ultimate goal is to prove that this is equivalent to `rot_right64`.
-/
def rot_right64_bytes (xs : Vector ℕ 8) (o : ℕ) : Vector ℕ 8 :=
  .ofFn fun ⟨ i, hi ⟩ => xs[i] / 2^o + (xs[(i + 1) % 8] % 2^o) * 2^(8-o)

-- unfold what rot_right64_bytes does on a U64
def rot_right64_u64 : U64 ℕ → ℕ → U64 ℕ
  | ⟨ x0, x1, x2, x3, x4, x5, x6, x7 ⟩, o => ⟨
    (x0 / 2^o) + (x1 % 2^o) * 2^(8-o),
    (x1 / 2^o) + (x2 % 2^o) * 2^(8-o),
    (x2 / 2^o) + (x3 % 2^o) * 2^(8-o),
    (x3 / 2^o) + (x4 % 2^o) * 2^(8-o),
    (x4 / 2^o) + (x5 % 2^o) * 2^(8-o),
    (x5 / 2^o) + (x6 % 2^o) * 2^(8-o),
    (x6 / 2^o) + (x7 % 2^o) * 2^(8-o),
    (x7 / 2^o) + (x0 % 2^o) * 2^(8-o),
  ⟩

-- these two are definitionally equal
lemma rot_right64_bytes_u64_eq (o : ℕ) (x : U64 ℕ) :
  rot_right64_bytes (to_elements x) o = to_elements (rot_right64_u64 x o) := rfl

lemma h_mod {offset : ℕ} (ho : offset < 8) {x0 x1 x2 x3 x4 x5 x6 x7 : ℕ} :
    (x0 + x1 * 256 + x2 * 256 ^ 2 + x3 * 256 ^ 3 + x4 * 256 ^ 4 + x5 * 256 ^ 5 + x6 * 256 ^ 6 + x7 * 256 ^ 7) %
      2^offset = x0 % 2^offset := by
  simp only [pow_one, Nat.add_mod, dvd_refl, Nat.mod_mod_of_dvd, gt_iff_lt, Nat.ofNat_pos,
    mul_mod_256_off ho, add_zero]
  rw [←Nat.pow_one 256, Nat.mod_mod, Nat.mod_mod, mul_mod_256_off ho _ _ (by linarith)]
  simp only [add_zero, dvd_refl, Nat.mod_mod_of_dvd]

lemma h_div {offset : ℕ} (ho : offset < 8) {x0 x1 x2 x3 x4 x5 x6 x7 : ℕ} :
    (x0 + x1 * 256 + x2 * 256 ^ 2 + x3 * 256 ^ 3 + x4 * 256 ^ 4 + x5 * 256 ^ 5 + x6 * 256 ^ 6 + x7 * 256 ^ 7) / 2 ^ offset
    = x0 / 2^offset + x1 * 2^(8 - offset) + x2 * 256 * 2^(8 - offset) +
    x3 * 256 ^ 2 * 2^(8 - offset) + x4 * 256 ^ 3 * 2^(8 - offset) +
    x5 * 256 ^ 4 * 2^(8 - offset) + x6 * 256 ^ 5 * 2^(8 - offset) +
    x7 * 256 ^ 6 * 2^(8 - offset) := by
  rw [←Nat.pow_one 256]
  repeat rw [Nat.add_div_of_dvd_left (by apply divides_256_two_power ho; linarith)]
  rw [mul_div_256_off ho 1 (by simp only [gt_iff_lt, Nat.lt_one_iff, pos_of_gt])]
  rw [mul_div_256_off ho 2 (by simp only [gt_iff_lt, Nat.ofNat_pos])]
  rw [mul_div_256_off ho 3 (by simp only [gt_iff_lt, Nat.ofNat_pos])]
  rw [mul_div_256_off ho 4 (by simp only [gt_iff_lt, Nat.ofNat_pos])]
  rw [mul_div_256_off ho 5 (by simp only [gt_iff_lt, Nat.ofNat_pos])]
  rw [mul_div_256_off ho 6 (by simp only [gt_iff_lt, Nat.ofNat_pos])]
  rw [mul_div_256_off ho 7 (by simp only [gt_iff_lt, Nat.ofNat_pos])]
  simp only [tsub_self, pow_zero, mul_one, Nat.add_one_sub_one, pow_one, Nat.reducePow,
    Nat.add_left_inj]

lemma h_x0_const {offset : ℕ} (ho : offset < 8) :
    2 ^ (8 - offset) * 256^7 = 2^(64 - offset) := by
  rw [show 256 = 2^8 by rfl, ←Nat.pow_mul, ←Nat.pow_add, add_comm]
  simp only [Nat.reduceMul, Nat.ofNat_pos, ne_eq, OfNat.ofNat_ne_one, not_false_eq_true,
    pow_right_inj₀]
  omega

theorem rotation64_bits_soundness {o : ℕ} (ho : o < 8) {x : U64 ℕ} :
    (rot_right64_u64 x o).value_nat = rot_right64 x.value_nat o := by
  -- simplify the goal
  simp only [rot_right64, rot_right64_u64, U64.value_nat]

  have offset_mod_64 : o % 64 = o := by
    apply Nat.mod_eq_of_lt
    linarith
  simp only [offset_mod_64]

  rw [h_mod ho]
  -- if the offset is zero, then it is trivial: it is a special case since
  -- in that case the rotation is a no-op
  by_cases h_offset : o = 0
  · simp [h_offset, Nat.mod_one]
  · rw [h_div ho]
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
