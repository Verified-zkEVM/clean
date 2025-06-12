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
open Utils.Rotation

/--
We define a bit rotation on "byte vectors" like u32 by splitting each byte
into low and high bits, and moving the lowest low bits to the top and concatenating
each resulting (high, low) pair again.

The ultimate goal is to prove that this is equivalent to `rot_right32`.
-/
def rot_right32_bytes (xs : Vector ℕ 4) (o : ℕ) : Vector ℕ 4 :=
  .ofFn fun ⟨ i, hi ⟩ => xs[i] / 2^o + (xs[(i + 1) % 4] % 2^o) * 2^(8-o)

-- unfold what rot_right32_bytes does on a U32
def rot_right32_u32 : U32 ℕ → ℕ → U32 ℕ
  | ⟨ x0, x1, x2, x3 ⟩, o => ⟨
    (x0 / 2^o) + (x1 % 2^o) * 2^(8-o),
    (x1 / 2^o) + (x2 % 2^o) * 2^(8-o),
    (x2 / 2^o) + (x3 % 2^o) * 2^(8-o),
    (x3 / 2^o) + (x0 % 2^o) * 2^(8-o),
  ⟩

-- these two are definitionally equal
lemma rot_right32_bytes_u32_eq (o : ℕ) (x : U32 ℕ) :
  rot_right32_bytes (to_elements x) o = to_elements (rot_right32_u32 x o) := rfl

lemma h_mod32 {offset : ℕ} (ho : offset < 8) {x0 x1 x2 x3 : ℕ} :
    (x0 + x1 * 256 + x2 * 256 ^ 2 + x3 * 256 ^ 3) %
      2 ^ offset = x0 % 2 ^ offset := by
  simp only [pow_one, Nat.add_mod, dvd_refl, Nat.mod_mod_of_dvd, gt_iff_lt, Nat.ofNat_pos,
    mul_mod_256_off ho, add_zero]
  rw [←Nat.pow_one 256, Nat.mod_mod, Nat.mod_mod, mul_mod_256_off ho _ _ (by linarith)]
  simp only [add_zero, dvd_refl, Nat.mod_mod_of_dvd]

lemma h_div32 {offset : ℕ} (ho : offset < 8) {x0 x1 x2 x3: ℕ} :
    (x0 + x1 * 256 + x2 * 256 ^ 2 + x3 * 256 ^ 3) / 2 ^ offset
    = x0 / 2^offset + x1 * 2^(8 - offset) + x2 * 256 * 2^(8 - offset) +
    x3 * 256 ^ 2 * 2^(8 - offset) := by
  rw [←Nat.pow_one 256]
  repeat rw [Nat.add_div_of_dvd_left (by apply divides_256_two_power ho; linarith)]

  rw [mul_div_256_off ho 1 (by simp only [gt_iff_lt, Nat.lt_one_iff, pos_of_gt])]
  rw [mul_div_256_off ho 2 (by simp only [gt_iff_lt, Nat.ofNat_pos])]
  rw [mul_div_256_off ho 3 (by simp only [gt_iff_lt, Nat.ofNat_pos])]
  simp only [tsub_self, pow_zero, mul_one, Nat.add_one_sub_one, pow_one, Nat.reducePow,
    Nat.add_left_inj]

lemma h_x0_const32 {offset : ℕ} (ho : offset < 8) :
    2 ^ (8 - offset) * 256^3 = 2^(32 - offset) := by
  rw [show 256 = 2^8 by rfl, ←Nat.pow_mul, ←Nat.pow_add, add_comm]
  simp only [Nat.reduceMul, Nat.ofNat_pos, ne_eq, OfNat.ofNat_ne_one, not_false_eq_true,
    pow_right_inj₀]
  omega

theorem rotation32_bits_soundness {o : ℕ} (ho : o < 8) {x : U32 ℕ} :
    (rot_right32_u32 x o).value_nat = rot_right32 x.value_nat o := by
  -- simplify the goal
  simp only [rot_right32, rot_right32_u32, U32.value_nat]

  have offset_mod_32 : o % 32 = o := Nat.mod_eq_of_lt (by linarith)
  simp only [offset_mod_32]
  rw [h_mod32 ho, h_div32 ho]

  -- proof technique: we care about only what happens to x0, all "internal" terms remain
  -- the same, and are just divided by 2^o
  rw [shifted_decomposition_eq ho]
  repeat rw [shifted_decomposition_eq'' ho (by simp only [gt_iff_lt, Nat.ofNat_pos])]
  simp only [Nat.add_one_sub_one, pow_one, add_mul, add_assoc]
  rw [←add_assoc _ _ (_ * 256 ^ 3), soundness_simp]
  nth_rw 4 [←add_assoc]
  rw [Nat.mul_right_comm _ 256, soundness_simp]
  nth_rw 2 [←add_assoc]
  rw [Nat.mul_right_comm _ 256, soundness_simp']
  rw [mul_assoc (x.x0 % 2 ^ o), h_x0_const32 ho]
  ac_rfl

end Gadgets.Rotation32.Theorems
