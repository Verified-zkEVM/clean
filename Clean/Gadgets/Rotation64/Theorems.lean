import Clean.Utils.Field
import Clean.Utils.Bitwise
import Clean.Types.U64
import Mathlib.Data.Nat.Bitwise

variable {p : ℕ} [Fact p.Prime]

namespace Gadgets.Rotation64.Theorems
open Bitwise (rot_right64)

def rot_right8 (x : Fin 256) (offset : Fin 8) : Fin 256 :=
  let low := x % (2^offset.val)
  let high := x / (2^offset.val)
  low * (2^(8 - offset.val)) + high

def rot_left8 (x : Fin 256) (offset : Fin 8) : Fin 256 :=
  let low := x % (2^(8 - offset.val))
  let high := x / (2^(8 - offset.val))
  low * (2^offset.val) + high


def rot_right64_eq_bv_rotate (x : ℕ) (h : x < 2^64) (offset : ℕ) :
    rot_right64 x offset = (x.toUInt64.toBitVec.rotateRight offset).toNat := by
  simp only [rot_right64]
  simp only [BitVec.toNat_rotateRight]
  simp only [Nat.shiftLeft_eq, Nat.mul_mod, dvd_refl, Nat.mod_mod_of_dvd]
  simp only [Nat.mod_mod, UInt64.toNat_toBitVec, UInt64.toNat_ofNat]

  by_cases cond : (offset % 64 = 0)
  · simp [cond, pow_zero, Nat.mod_one, tsub_zero, Nat.reducePow, zero_mul, Nat.div_one,
    zero_add, Nat.shiftRight_zero, Nat.mod_self, mul_zero, Nat.zero_mod, Nat.or_zero]
    symm
    apply Nat.mod_eq_of_lt
    linarith

  · have h1 : 2^(64 - offset%64) < 2^64 := by
      apply Nat.pow_lt_pow_of_lt
      · linarith
      · simp only [tsub_lt_self_iff, Nat.ofNat_pos, true_and]
        simp [Nat.ne_zero_iff_zero_lt] at cond
        assumption
    rw [Nat.mod_eq_of_lt h1, Nat.shiftRight_eq_div_pow]
    have low_lt : x / 2 ^ (offset % 64) < 2 ^ (64 - offset % 64) := by
      rw [Nat.div_lt_iff_lt_mul (by apply Nat.two_pow_pos)]
      rw [←Nat.pow_add, Nat.sub_add_cancel (by
        have : offset % 64 < 64 := Nat.mod_lt offset (by linarith)
        linarith)]
      linarith
    rw [mul_comm, Nat.two_pow_add_eq_or_of_lt low_lt, Nat.or_comm]
    congr
    · simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.reducePow]
      symm
      apply Nat.mod_eq_of_lt
      assumption
    rw [Nat.mul_comm]
    rw [←Nat.shiftLeft_eq, ←Nat.shiftLeft_eq, ←Nat.one_shiftLeft]

    let x_bv := x.toUInt64
    let offset_bv := (offset % 64).toUInt64
    have h_sat : offset_bv < 64 → offset_bv > 0 →
        (x_bv % 1<<<offset_bv) <<< (64 - offset_bv) = x_bv <<< (64 - offset_bv) := by
      bv_decide

    have offset_bv_lt : offset_bv < 64 := by
      simp only [offset_bv]
      simp only [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat, UInt64.reduceToNat]
      apply Nat.mod_lt_of_lt
      apply Nat.mod_lt offset (by linarith)

    have offset_bv_pos : offset_bv > 0 := by
      simp only [Nat.toUInt64_eq, gt_iff_lt, offset_bv]
      have := Nat.pos_of_ne_zero cond
      rw [UInt64.lt_ofNat_iff]
      simp only [UInt64.toNat_zero, offset_bv]
      · assumption
      · simp [UInt64.size]
        have : offset % 64 < 64 := Nat.mod_lt offset (by linarith)
        linarith

    specialize h_sat offset_bv_lt offset_bv_pos
    apply_fun UInt64.toNat at h_sat

    simp only [UInt64.toNat_shiftLeft, UInt64.toNat_mod, UInt64.toNat_ofNat,
      UInt64.reduceToNat, x_bv, offset_bv] at h_sat
    simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.one_mod, Nat.reduceDvd,
      Nat.mod_mod_of_dvd, dvd_refl, offset_bv, x_bv] at h_sat
    rw [Nat.mod_eq_of_lt h] at h_sat

    have h' : UInt64.ofNat (offset % 64) ≤ 64 := by
      have : offset % 64 < 64 := Nat.mod_lt offset (by linarith)
      rw [UInt64.ofNat_le_iff]
      · simp only [UInt64.reduceToNat, ge_iff_le, offset_bv, x_bv]
        linarith
      · simp [UInt64.size]
        linarith
    rw [UInt64.toNat_sub_of_le _ _ h'] at h_sat
    simp only [Nat.reduceDvd, Nat.mod_mod_of_dvd, dvd_refl, UInt64.reduceToNat,
      UInt64.toNat_ofNat', offset_bv, x_bv] at h_sat

    have h_eq : offset % 64 % 2^64 = offset % 64 := by
      apply Nat.mod_eq_of_lt
      have : offset % 64 < 64 := Nat.mod_lt offset (by linarith)
      linarith
    rw [h_eq, Nat.mod_mod] at h_sat
    simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat', dvd_refl, Nat.mod_mod_of_dvd,
      offset_bv, x_bv]

    rw [show x % 2^64 = x by
      apply Nat.mod_eq_of_lt
      linarith]

    have h_eq' : (64 - offset % 64) % 64 = 64 - offset % 64 := by
      apply Nat.mod_eq_of_lt
      have : offset % 64 < 64 := Nat.mod_lt offset (by linarith)
      simp only [tsub_lt_self_iff, Nat.ofNat_pos, true_and, gt_iff_lt, offset_bv, x_bv]
      exact Nat.pos_of_ne_zero cond
    rw [h_eq'] at h_sat
    rw [←h_sat]

    have h_eq2 : (1 <<< (offset % 64)) % 2^64 = (1 <<< (offset % 64)) := by
      apply Nat.mod_eq_of_lt
      rw [Nat.one_shiftLeft]
      apply Nat.pow_lt_pow_of_lt
      linarith
      apply Nat.mod_lt
      linarith
    rw [h_eq2]

    have h_eq3 : (x % 1 <<< (offset % 64)) <<< (64 - offset % 64) % 2 ^ 64 =
        (x % 1 <<< (offset % 64)) <<< (64 - offset % 64) := by
      apply Nat.mod_eq_of_lt
      have eq : 64 = (offset % 64) + (64 - (offset % 64)) := by
        rw [Nat.add_sub_of_le]
        apply Nat.le_of_lt
        apply Nat.mod_lt
        linarith
      rw (occs:= .pos [4]) [eq]
      apply Nat.shiftLeft_lt
      rw [Nat.one_shiftLeft]
      apply Nat.mod_lt
      simp only [gt_iff_lt, Nat.ofNat_pos, pow_pos, offset_bv, x_bv]

    rw [h_eq3]

lemma rot_right64_def (x : ℕ) (off : ℕ) (hx : x < 2^64) :
    rot_right64 x off = x >>> (off % 64) ||| x <<< (64 - off % 64) % 2 ^ 64 := by
  rw [rot_right64_eq_bv_rotate _ hx]
  simp only [Nat.toUInt64_eq, BitVec.toNat_rotateRight, UInt64.toNat_toBitVec, UInt64.toNat_ofNat']
  rw [show x % 2^64 = x by apply Nat.mod_eq_of_lt hx]

lemma rot_mod_64 (x : ℕ) (off1 off2 : ℕ) (h : off1 = off2 % 64) :
    rot_right64 x off1 = rot_right64 x off2 := by
  simp only [rot_right64]
  rw [←h]
  have h' : off2 % 64 < 64 := Nat.mod_lt off2 (by linarith)
  rw [←h] at h'
  rw [Nat.mod_eq_of_lt h']

lemma rot_right64_fin (x : ℕ) (offset : Fin 64) :
    rot_right64 x offset.val = x % (2^offset.val) * (2^(64 - offset.val)) + x / (2^offset.val) := by
  simp only [rot_right64]
  rw [Nat.mod_eq_of_lt offset.is_lt]

def to_bits (n : ℕ) (x : ℕ) : Vector ℕ n :=
  .mapRange n fun i => if x.testBit i then 1 else 0

def from_bits {n : ℕ} (bits : Vector ℕ n) : ℕ :=
  Fin.foldl n (fun acc ⟨i, _⟩ => acc + bits[i] * 2^i) 0

lemma to_bits_from_bits_aux {n: ℕ} (bits : Vector ℕ n)
  (h_bits : ∀ (i : ℕ) (hi : i < n), bits[i] = 0 ∨ bits[i] = 1) :
    (from_bits bits) < 2^n ∧ to_bits n (from_bits bits) = bits := by
  rw [Vector.ext_iff]
  simp only [from_bits, to_bits, Vector.getElem_mapRange]
  induction n with
  | zero => simp_all
  | succ n ih =>
    simp only [Fin.foldl_succ_last, Fin.coe_castSucc, Fin.val_last]
    let bits' : Vector ℕ n := bits.pop
    have h_bits' : ∀ j (hj : j < n), bits'[j] = 0 ∨ bits'[j] = 1
      | j, hj => by
        simp only [Vector.getElem_pop', bits']
        exact h_bits j (Nat.lt_succ_of_lt hj)

    have h_bits_n : bits[n] = 0 ∨ bits[n] = 1 := h_bits n (Nat.lt_succ_self _)
    obtain ⟨ ih_lt, ih_eq ⟩ := ih bits' h_bits'

    simp only [Vector.getElem_pop', bits'] at ih_eq ih_lt

    let xn : ℕ := Fin.foldl n (fun acc ⟨i, _⟩ => acc + bits[i] * (2 ^ i)) 0
    have : bits[n] ≤ 1 := by rcases h_bits_n <;> simp only [zero_le, le_refl, *]
    have h_lt : xn + bits[n] * 2^n < 2^(n + 1) := by
      have : bits[n] * 2^n ≤ 1 * 2^n := Nat.mul_le_mul_right (2 ^ n) (by linarith)
      rw [Nat.pow_succ']
      linarith

    constructor
    · exact h_lt
    · intro i hi
      rw [mul_comm _ (2^n), add_comm _ (2^n * _), Nat.testBit_two_pow_mul_add _ ih_lt]
      by_cases hin : i < n <;> simp only [hin, reduceIte]
      · exact ih_eq i hin
      · have : n = i := by linarith
        subst this
        rcases h_bits_n <;> simp [*, ZMod.val_one]

/-- `to_bits` is a left-inverse of `from_bits` -/
theorem to_bits_from_bits {n: ℕ} (bits : Vector ℕ n)
  (h_bits : ∀ (i : ℕ) (hi : i < n), bits[i] = 0 ∨ bits[i] = 1) :
    to_bits n (from_bits bits) = bits := (to_bits_from_bits_aux bits h_bits).right

/-- the result of `from_bits` is less than 2^n -/
theorem from_bits_lt {n: ℕ} (bits : Vector ℕ n)
  (h_bits : ∀ (i : ℕ) (hi : i < n), bits[i] = 0 ∨ bits[i] = 1) :
    (from_bits bits) < 2^n := (to_bits_from_bits_aux bits h_bits).left

/-- on numbers less than `2^n`, `to_bits n` is injective -/
theorem to_bits_injective (n: ℕ) {x y : ℕ} : x < 2^n → y < 2^n →
    to_bits n x = to_bits n y → x = y := by
  intro hx hy h_eq
  rw [Vector.ext_iff] at h_eq
  simp only [to_bits, Vector.getElem_mapRange] at h_eq
  have h_eq' : ∀ i (hi : i < n), x.testBit i = y.testBit i := by
    intro i hi
    specialize h_eq i hi
    by_cases hx_i : x.testBit i <;> by_cases hy_i : y.testBit i <;>
      simp_all

  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < n
  · exact h_eq' i hi
  · have : n ≤ i := by linarith
    have : 2^n ≤ 2^i := Nat.pow_le_pow_of_le (a:=2) (by norm_num) this
    replace hx : x < 2^i := by linarith
    replace hy : y < 2^i := by linarith
    rw [Nat.testBit_lt_two_pow hx, Nat.testBit_lt_two_pow hy]

/-- on numbers less than `2^n`, `to_bits` is a right-inverse of `from_bits` -/
theorem from_bits_to_bits {n: ℕ} {x : ℕ} (hx : x < 2^n) :
    from_bits (to_bits n x) = x := by
  have h_bits : ∀ i (hi : i < n), (to_bits n x)[i] = 0 ∨ (to_bits n x)[i] = 1 := by
    intro i hi; simp [to_bits]
  apply to_bits_injective n (from_bits_lt _ h_bits) hx
  rw [to_bits_from_bits _ h_bits]


lemma rot_right64_testBit_of_lt (x r i : ℕ) (h : x < 2^64) (hi : i < 64 - r % 64) :
    (rot_right64 x r).testBit i = x.testBit (r % 64 + i) := by
  rw [rot_right64_def _ _ h, Nat.testBit_or, Nat.testBit_shiftRight, Nat.testBit_mod_two_pow,
    Nat.testBit_shiftLeft]
  have h_i : 64 - r % 64 ≤ 64 := by apply Nat.sub_le
  have h_i' : i < 64 := by linarith
  simp [h_i']
  omega

lemma rot_right64_testBit_of_ge (x r i : ℕ) (h : x < 2^64) (hi : i ≥ 64 - r % 64) :
    (rot_right64 x r).testBit i = (decide (i < 64) && x.testBit (i - (64 - r % 64))) := by
  rw [rot_right64_def _ _ h, Nat.testBit_or, Nat.testBit_mod_two_pow]
  suffices (x >>> (r % 64)).testBit i = false by
    simp [this]
    by_cases h : i < 64 <;> simp [h]; omega

  simp only [Nat.testBit_shiftRight]
  apply Nat.testBit_lt_two_pow
  have : 2^64 ≤ 2^(r % 64 + i) := by
    apply Nat.pow_le_pow_right
    · linarith
    omega
  linarith

lemma rot_right64_testBit (x r i : ℕ) (h : x < 2^64) :
    (rot_right64 x r).testBit i =
    if i < 64 - r % 64 then
      x.testBit (r % 64 + i)
    else (decide (i < 64) && x.testBit (i - (64 - r % 64))) := by

  split
  · rw [rot_right64_testBit_of_lt]
    repeat omega
  · rw [rot_right64_testBit_of_ge]
    repeat omega


theorem rot_right64_to_bits (x r : ℕ) (h : x < 2^64):
    to_bits 64 (rot_right64 x r) = (to_bits 64 x).rotate r := by
  simp [to_bits, Vector.rotate]
  ext i hi
  · simp
  simp at ⊢ hi
  rw [rot_right64_testBit]
  simp [List.getElem_rotate, hi]
  split <;> (congr; omega)
  linarith


theorem rot_right64_lt (x r : ℕ) (h : x < 2^64) :
    rot_right64 x r < 2^64 := by
  rw [rot_right64_def _ _ h]
  have := Nat.shiftRight_le x (r % 64)
  apply Nat.or_lt_two_pow <;> omega


theorem rot_right_composition (x n m : ℕ) (h : x < 2^64) :
    rot_right64 (rot_right64 x n) m = rot_right64 x (n + m) := by
  have h1 : (rot_right64 (rot_right64 x n) m) < 2^64 := by
    repeat apply rot_right64_lt
    assumption

  have h2 : (rot_right64 x (n + m)) < 2^64 := by
    apply rot_right64_lt
    assumption

  -- suffices to show equality over bits
  suffices to_bits 64 (rot_right64 (rot_right64 x n) m) = to_bits 64 (rot_right64 x (n + m)) by
    exact to_bits_injective 64 h1 h2 this

  -- rewrite rotation over bits
  rw [rot_right64_to_bits _ _ h,
    rot_right64_to_bits _ _ (by apply rot_right64_lt; assumption),
    rot_right64_to_bits _ _ h]

  -- now this is easy, it is just rotation composition over vectors
  rw [Vector.rotate_rotate]


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



end Gadgets.Rotation64.Theorems
