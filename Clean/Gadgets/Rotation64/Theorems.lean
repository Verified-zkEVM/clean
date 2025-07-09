import Clean.Utils.Field
import Clean.Utils.Bitwise
import Clean.Utils.Rotation
import Clean.Types.U64

variable {p : ℕ} [Fact p.Prime]
variable [p_large_enough: Fact (p > 2^16 + 2^8)]

namespace Gadgets.Rotation64.Theorems
open Utils.Rotation

/--
We define a bit rotation on "byte vectors" like u64 by splitting each byte
into low and high bits, and moving the lowest low bits to the top and concatenating
each resulting (high, low) pair again.

The ultimate goal is to prove that this is equivalent to `rotRight64`.
-/
def rotRight64_bytes (xs : Vector ℕ 8) (o : ℕ) : Vector ℕ 8 :=
  .ofFn fun ⟨ i, hi ⟩ => xs[i] / 2^o + (xs[(i + 1) % 8] % 2^o) * 2^(8-o)

-- unfold what rotRight64_bytes does on a U64
def rotRight64_u64 : U64 ℕ → ℕ → U64 ℕ
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
lemma rotRight64_bytes_u64_eq (o : ℕ) (x : U64 ℕ) :
  rotRight64_bytes x.toLimbs o = (rotRight64_u64 x o).toLimbs := rfl

lemma h_mod {o : ℕ} (ho : o < 8) {x0 x1 x2 x3 x4 x5 x6 x7 : ℕ} :
    (x0 + x1 * 256 + x2 * 256 ^ 2 + x3 * 256 ^ 3 + x4 * 256 ^ 4 + x5 * 256 ^ 5 + x6 * 256 ^ 6 + x7 * 256 ^ 7) %
      2^o = x0 % 2^o := by
  nth_rw 1 [←Nat.pow_one 256]
  repeat rw [Nat.add_mod, mul_mod256_off ho _ _ (by trivial), add_zero, Nat.mod_mod]

lemma h_div {o : ℕ} (ho : o < 8) {x0 x1 x2 x3 x4 x5 x6 x7 : ℕ} :
    (x0 + x1 * 256 + x2 * 256^2 + x3 * 256^3 + x4 * 256^4 + x5 * 256^5 + x6 * 256^6 + x7 * 256^7) / 2 ^ o
    = x0 / 2^o + x1 * 2^(8-o) + x2 * 256 * 2^(8-o) + x3 * 256^2 * 2^(8-o) + x4 * 256^3 * 2^(8-o) +
    x5 * 256^4 * 2^(8-o) + x6 * 256^5 * 2^(8-o) + x7 * 256^6 * 2^(8-o) := by
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

lemma h_x0_const {o : ℕ} (ho : o < 8) :
    2^(8 - o) * 256^7 = 2^(64 - o) := by
  rw [show 256 = 2^8 by rfl, ←Nat.pow_mul, ←Nat.pow_add, pow_right_inj₀ (by norm_num) (by norm_num)]
  omega

theorem rotation64_bits_soundness {o : ℕ} (ho : o < 8) {x : U64 ℕ} :
    (rotRight64_u64 x o).valueNat = rotRight64 x.valueNat o := by
  -- simplify the goal
  simp only [rotRight64, rotRight64_u64, U64.valueNat]

  have offset_mod_64 : o % 64 = o := Nat.mod_eq_of_lt (by linarith)
  simp only [offset_mod_64]
  rw [h_mod ho, h_div ho]

  -- proof technique: we care about only what happens to x0, all "internal" terms remain
  -- the same, and are just divided by 2^o
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
