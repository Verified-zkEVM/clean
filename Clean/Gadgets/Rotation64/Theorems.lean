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
  (rot_right64_bytes (to_elements x) o) = to_elements (rot_right64_u64 x o) := rfl

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
    y0 y1 y2 y3 y4 y5 y6 y7 : ℕ
  }
  (eq0 : y0 = (x0 / 2^o) + (x1 % 2^o) * 2^(8-o))
  (eq1 : y1 = (x1 / 2^o) + (x2 % 2^o) * 2^(8-o))
  (eq2 : y2 = (x2 / 2^o) + (x3 % 2^o) * 2^(8-o))
  (eq3 : y3 = (x3 / 2^o) + (x4 % 2^o) * 2^(8-o))
  (eq4 : y4 = (x4 / 2^o) + (x5 % 2^o) * 2^(8-o))
  (eq5 : y5 = (x5 / 2^o) + (x6 % 2^o) * 2^(8-o))
  (eq6 : y6 = (x6 / 2^o) + (x7 % 2^o) * 2^(8-o))
  (eq7 : y7 = (x7 / 2^o) + (x0 % 2^o) * 2^(8-o)) :

    let x_val := x0 + x1 * 256 + x2 * 256^2 + x3 * 256^3 + x4 * 256^4 +
      x5 * 256^5 + x6 * 256^6 + x7 * 256^7

    let y_val := y0 + y1 * 256 + y2 * 256^2 + y3 * 256^3 + y4 * 256^4 +
      y5 * 256^5 + y6 * 256^6 + y7 * 256^7

    y_val = rot_right64 x_val o := by

  -- simplify the goal
  simp only [rot_right64]
  rw [eq0, eq1, eq2, eq3, eq4, eq5, eq6, eq7]

  have offset_mod_64 : o % 64 = o := by
    apply Nat.mod_eq_of_lt
    linarith
  simp only [offset_mod_64]

  rw [h_mod (offset := ⟨o, ho⟩)]
  simp only
  -- if the offset is zero, then it is trivial: it is a special case since
  -- in that case the rotation is a no-op
  by_cases h_offset : o = 0
  · simp [h_offset, Nat.mod_one]
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

theorem rotation64_bits_soundness' {o : ℕ} (ho : o < 8) {x : U64 ℕ} :
    (rot_right64_u64 x o).value_nat = rot_right64 x.value_nat o := by
  set y := rot_right64_u64 x o
  have heq : y = rot_right64_u64 x o := rfl
  rcases x with ⟨x0, x1, x2, x3, x4, x5, x6, x7⟩
  rcases y with ⟨y0, y1, y2, y3, y4, y5, y6, y7⟩
  simp only [U64.mk.injEq, rot_right64_u64] at heq
  simp only [U64.value_nat]
  apply rotation64_bits_soundness o ho <;> simp_all
end Gadgets.Rotation64.Theorems
