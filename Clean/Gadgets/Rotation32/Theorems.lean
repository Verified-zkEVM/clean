import Clean.Utils.Field
import Clean.Utils.Bitwise
import Clean.Types.U32

variable {p : ℕ} [Fact p.Prime]

namespace Gadgets.Rotation32.Theorems
open Bitwise (rot_right32)

omit [Fact (Nat.Prime p)] in
lemma soundnessCase1 (x0 x1 x2 x3 : F p) (as : ZMod.val x0 < 256 ∧ ZMod.val x1 < 256 ∧ ZMod.val x2 < 256 ∧ ZMod.val x3 < 256) : { x0 := x1, x1 := x2, x2 := x3, x3 := x0 : U32 _}.value =
  rot_right32 { x0 := x0, x1 := x1, x2 := x2, x3 := x3 : U32 _}.value 8 := by
  simp only [U32.value, rot_right32]
  rw [
    show (8 % 32) = 8 by norm_num,
    show (32 - 8) = 24 by norm_num,
  ]
  have x0_pos : 0 ≤ x0.val := by exact Nat.zero_le _
  zify at *
  set x0 : ℤ := x0.val.cast
  set x1 : ℤ := x1.val.cast
  set x2 : ℤ := x2.val.cast
  set x3 : ℤ := x3.val.cast

  have powers_mod :
    (16777216 : ℤ) % 256 = 0 ∧
    (65536 : ℤ) % 256 = 0 := by norm_num

  have h : (x0 + x1 * 256 + x2 * 256 ^ 2 + x3 * 256 ^ 3) % 2 ^ 8 = x0 := by
    repeat
      ring_nf
      rw [Int.add_emod, Int.mul_emod]
      simp only [powers_mod]
      norm_num
    rw [Int.emod_eq_of_lt x0_pos (by linarith)]

  have h' : (x0 + x1 * 256 + x2 * 256 ^ 2 + x3 * 256 ^ 3) / 2 ^ 8 =
      x1 + x2 * 256 + x3 * 256 ^ 2 := by

    repeat
      ring_nf
      rw [Int.add_ediv_of_dvd_right (by
        rw [Int.dvd_iff_emod_eq_zero, Int.mul_emod]
        try rw [show (16777216 : ℤ) % 256 = 0 by rfl]
        try rw [show (65536 : ℤ) % 256 = 0 by rfl]
        rfl)]
      rw [Int.mul_ediv_assoc _ (by norm_num)]
      norm_num
    rw [Int.ediv_eq_zero_of_lt (by simp only [x0_pos]) (by simp only [as])]

  rw [h, h']
  ring

omit [Fact (Nat.Prime p)] in
lemma soundnessCase2 (x0 x1 x2 x3 : F p) (as : ZMod.val x0 < 256 ∧ ZMod.val x1 < 256 ∧ ZMod.val x2 < 256 ∧ ZMod.val x3 < 256) : { x0 := x2, x1 := x3, x2 := x0, x3 := x1 : U32 _}.value =
  rot_right32 { x0 := x0, x1 := x1, x2 := x2, x3 := x3 : U32 _}.value 16 := by
  simp only [U32.value, rot_right32]
  rw [
    show (16 % 32) = 16 by norm_num,
    show (32 - 16) = 16 by norm_num,
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

  have powers_mod :
    (16777216 : ℤ) % 65536 = 0 := by norm_num

  have h : (x0 + x1 * 256 + x2 * 256 ^ 2 + x3 * 256 ^ 3) % (2 ^ 16) = x0 + x1 * 256 := by
    norm_num
    repeat
      rw [Int.add_emod, Int.mul_emod]
      simp only [powers_mod]
      norm_num
    rw [Int.emod_eq_of_lt x0_x1_pos (by linarith)]

  have h' : (x0 + x1 * 256 + x2 * 256 ^ 2 + x3 * 256 ^ 3) / 2 ^ 16 =
      x2 + x3 * 256 := by

    repeat
      norm_num
      rw [Int.add_ediv_of_dvd_right (by
        rw [Int.dvd_iff_emod_eq_zero, Int.mul_emod]
        try rw [show (16777216 : ℤ) % 65536 = 0 by rfl]
        rfl)]
      rw [Int.mul_ediv_assoc _ (by norm_num)]
      norm_num
    rw [Int.ediv_eq_zero_of_lt (by simp only [x0_x1_pos]) (by linarith)]

  rw [h, h']
  ring

omit [Fact (Nat.Prime p)] in
lemma soundnessCase3 (x0 x1 x2 x3 : F p) (as : ZMod.val x0 < 256 ∧ ZMod.val x1 < 256 ∧ ZMod.val x2 < 256 ∧ ZMod.val x3 < 256) : { x0 := x3, x1 := x0, x2 := x1, x3 := x2 : U32 _}.value =
  rot_right32 { x0 := x0, x1 := x1, x2 := x2, x3 := x3 : U32 _}.value 24 := by
  simp only [U32.value, rot_right32]
  rw [
    show (24 % 32) = 24 by norm_num,
    show (32 - 24) = 8 by norm_num,
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

  have h : (x0 + x1 * 256 + x2 * 256 ^ 2 + x3 * 256 ^ 3) % (2 ^ 24) = x0 + x1 * 256 + x2 * 256 ^ 2 := by
    norm_num
    rw [Int.add_emod, Int.mul_emod]
    norm_num
    rw [Int.emod_eq_of_lt x2_pos (by linarith)]
    rw [Int.emod_eq_of_lt x0_x1_x2_pos (by linarith)]

  have h' : (x0 + x1 * 256 + x2 * 256 ^ 2 + x3 * 256 ^ 3) / 2 ^ 24 = x3 := by
    repeat
      norm_num
      rw [Int.add_ediv_of_dvd_right (by
        rw [Int.dvd_iff_emod_eq_zero, Int.mul_emod]
        rfl)]
      rw [Int.mul_ediv_assoc _ (by norm_num)]
      norm_num
    rw [Int.ediv_eq_zero_of_lt (by simp only [x0_x1_x2_pos]) (by linarith)]

  rw [h, h']
  ring

end Gadgets.Rotation32.Theorems
