import Clean.Gadgets.Addition8.Addition8FullCarry
import Clean.Types.U64
import Clean.Gadgets.Rotation64.Theorems

namespace Gadgets.Rotation64Bytes
variable {p : ℕ} [Fact p.Prime]

open Gadgets.Rotation64.Theorems (rot_right64)

structure Inputs (F : Type) where
  x: U64 F

instance instProvableTypeInputs : ProvableType Inputs where
  size := ProvableType.size U64
  to_elements x := (ProvableType.to_elements x.x)
  from_elements v :=
    let ⟨ .mk [x0, x1, x2, x3, x4, x5, x6, x7], _ ⟩ := v
    ⟨ ⟨ x0, x1, x2, x3, x4, x5, x6, x7 ⟩ ⟩

structure Outputs (F : Type) where
  z: U64 F

instance instProvableTypeOutputs : ProvableType Outputs where
  size := ProvableType.size U64
  to_elements x := (ProvableType.to_elements x.z)
  from_elements v :=
    let ⟨ .mk [z0, z1, z2, z3, z4, z5, z6, z7], _ ⟩ := v
    ⟨ ⟨ z0, z1, z2, z3, z4, z5, z6, z7 ⟩ ⟩

/--
  Rotate the 64-bit integer by increments of 8 positions
  This gadget does not introduce constraints
-/
def rot64_bytes (offset : Fin 8) (input : Var Inputs (F p)) : Circuit (F p) (Var Outputs (F p)) := do
  let ⟨x0, x1, x2, x3 , x4, x5, x6, x7⟩ := input
  let offset := offset.val

  if offset = 0 then
    return ⟨ x0, x1, x2, x3, x4, x5, x6, x7 ⟩
  else if offset = 1 then
    return ⟨ x1, x2, x3, x4, x5, x6, x7, x0 ⟩
  else if offset = 2 then
    return ⟨ x2, x3, x4, x5, x6, x7, x0, x1 ⟩
  else if offset = 3 then
    return ⟨ x3, x4, x5, x6, x7, x0, x1, x2 ⟩
  else if offset = 4 then
    return ⟨ x4, x5, x6, x7, x0, x1, x2, x3 ⟩
  else if offset = 5 then
    return ⟨ x5, x6, x7, x0, x1, x2, x3, x4 ⟩
  else if offset = 6 then
    return ⟨ x6, x7, x0, x1, x2, x3, x4, x5 ⟩
  else
    return ⟨ x7, x0, x1, x2, x3, x4, x5, x6 ⟩

def assumptions (input : Inputs (F p)) := input.x.is_normalized

def spec (offset : Fin 8) (input : Inputs (F p)) (out: Outputs (F p)) :=
  let ⟨x⟩ := input
  let ⟨y⟩ := out
  y.value = rot_right64 x.value (offset.val * 8)

omit [Fact (Nat.Prime p)] in
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

omit [Fact (Nat.Prime p)] in
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

omit [Fact (Nat.Prime p)] in
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

omit [Fact (Nat.Prime p)] in
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

omit [Fact (Nat.Prime p)] in
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

omit [Fact (Nat.Prime p)] in
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

omit [Fact (Nat.Prime p)] in
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

theorem soundness (off : Fin 8) : Soundness (F p) Inputs  Outputs (rot64_bytes off) assumptions (spec off) := by
  rintro i0 env ⟨ x0_var, x1_var, x2_var, x3_var, x4_var, x5_var, x6_var, x7_var ⟩ ⟨ x0, x1, x2, x3, x4, x5, x6, x7 ⟩ h_inputs as h

  have h_x0 : x0_var.eval env = x0 := by injections h_inputs
  have h_x1 : x1_var.eval env = x1 := by injections h_inputs
  have h_x2 : x2_var.eval env = x2 := by injections h_inputs
  have h_x3 : x3_var.eval env = x3 := by injections h_inputs
  have h_x4 : x4_var.eval env = x4 := by injections h_inputs
  have h_x5 : x5_var.eval env = x5 := by injections h_inputs
  have h_x6 : x6_var.eval env = x6 := by injections h_inputs
  have h_x7 : x7_var.eval env = x7 := by injections h_inputs
  clear h_inputs
  clear h

  dsimp only [assumptions, U64.is_normalized] at as
  fin_cases off
  · simp [circuit_norm, rot64_bytes, spec, circuit_norm, Circuit.output, monad_norm, StateT.pure, pure]
    rw [h_x0, h_x1, h_x2, h_x3, h_x4, h_x5, h_x6, h_x7]
    simp [U64.value, rot_right64, Nat.mod_one]

  · simp [circuit_norm, rot64_bytes, spec, circuit_norm, Circuit.output, monad_norm, StateT.pure, pure]
    rw [h_x0, h_x1, h_x2, h_x3, h_x4, h_x5, h_x6, h_x7]
    exact soundnessCase1 x0 x1 x2 x3 x4 x5 x6 x7 as

  · simp [circuit_norm, rot64_bytes, spec, circuit_norm, Circuit.output, monad_norm, StateT.pure, pure]
    rw [h_x0, h_x1, h_x2, h_x3, h_x4, h_x5, h_x6, h_x7]
    exact soundnessCase2 x0 x1 x2 x3 x4 x5 x6 x7 as

  · simp [circuit_norm, rot64_bytes, spec, circuit_norm, Circuit.output, monad_norm, StateT.pure, pure, show (3 : Fin 8).val = 3 by rfl]
    rw [h_x0, h_x1, h_x2, h_x3, h_x4, h_x5, h_x6, h_x7]
    exact soundnessCase3 x0 x1 x2 x3 x4 x5 x6 x7 as

  · simp [circuit_norm, rot64_bytes, spec, circuit_norm, Circuit.output, monad_norm, StateT.pure, pure, show (4 : Fin 8).val = 4 by rfl]
    rw [h_x0, h_x1, h_x2, h_x3, h_x4, h_x5, h_x6, h_x7]
    exact soundnessCase4 x0 x1 x2 x3 x4 x5 x6 x7 as

  · simp [circuit_norm, rot64_bytes, spec, circuit_norm, Circuit.output, monad_norm, StateT.pure, pure, show (5 : Fin 8).val = 5 by rfl]
    rw [h_x0, h_x1, h_x2, h_x3, h_x4, h_x5, h_x6, h_x7]
    exact soundnessCase5 x0 x1 x2 x3 x4 x5 x6 x7 as

  · simp [circuit_norm, rot64_bytes, spec, circuit_norm, Circuit.output, monad_norm, StateT.pure, pure, show (6 : Fin 8).val = 6 by rfl]
    rw [h_x0, h_x1, h_x2, h_x3, h_x4, h_x5, h_x6, h_x7]
    exact soundnessCase6 x0 x1 x2 x3 x4 x5 x6 x7 as

  · simp [circuit_norm, rot64_bytes, spec, circuit_norm, Circuit.output, monad_norm, StateT.pure, pure, show (7 : Fin 8).val = 7 by rfl]
    rw [h_x0, h_x1, h_x2, h_x3, h_x4, h_x5, h_x6, h_x7]
    exact soundnessCase7 x0 x1 x2 x3 x4 x5 x6 x7 as

theorem completeness (off : Fin 8) : Completeness (F p) Inputs Outputs (rot64_bytes off) assumptions := by
  rintro i0 env ⟨ x0_var, x1_var, x2_var, x3_var, x4_var, x5_var, x6_var, x7_var ⟩ henv ⟨ x0, x1, x2, x3, x4, x5, x6, x7 ⟩ _
  fin_cases off
  repeat
    · simp [circuit_norm]

def circuit (off : Fin 8) : FormalCircuit (F p) Inputs Outputs where
  main := rot64_bytes off
  assumptions := assumptions
  spec := spec off
  soundness := soundness off
  completeness := completeness off
  -- technical condition needed for subcircuit consistency. usually automatically proved by `rfl`.
  initial_offset_eq: ∀ var, ∀ n, ((rot64_bytes off) var |>.operations n).initial_offset = n := by
    intros
    fin_cases off
    repeat
      rfl
end Gadgets.Rotation64Bytes
