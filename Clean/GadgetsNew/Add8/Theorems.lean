import Mathlib.Algebra.Field.Basic
import Mathlib.Data.ZMod.Basic
import Clean.Utils.Primes
import Clean.Utils.Vector
import Clean.Circuit.Expression
import Clean.Circuit.Provable
import Clean.Circuit.Basic
import Clean.Utils.Field

namespace Add8Theorems
variable {p : ℕ} [Fact p.Prime]
variable [p_large_enough: Fact (p > 512)]


/-
  First part of the soundness direction: case of zero carry
-/
theorem soundness_zero_carry (x y out carry_in: F p):
    x.val < 256 -> y.val < 256 -> out.val < 256  -> carry_in.val < 2 ->
    (carry_in + x + y - out = 0 -> (out.val = (carry_in.val + x.val + y.val) % 256
    ∧ (carry_in.val + x.val + y.val) / 256 = 0)) := by
  intros hx hy hout hb h
  -- we show that the sum do not overflow the field
  have not_wrap := FieldUtils.byte_sum_and_bit_do_not_wrap x y carry_in hx hy hb
  rw [sub_eq_zero] at h
  apply_fun ZMod.val at h
  constructor
  · rw [←not_wrap, h, Nat.mod_eq_of_lt hout]
  · apply Nat.div_eq_of_lt
    rw [←not_wrap, h]
    assumption

/-
  Second part of the soundness direction: case of one carry
-/
theorem soundness_one_carry (x y out carry_in: F p):
    x.val < 256 -> y.val < 256 -> out.val < 256 -> carry_in.val < 2 ->
    carry_in + x + y - out - 256 = 0 -> (out.val = (carry_in.val + x.val + y.val) % 256
    ∧ (carry_in.val + x.val + y.val) / 256 = 1) := by

  intros hx hy hout hb h
  have xy_not_wrap := FieldUtils.byte_sum_do_not_wrap x y hx hy
  have not_wrap := FieldUtils.byte_sum_and_bit_do_not_wrap x y carry_in hx hy hb
  have out_plus_256_not_wrap := FieldUtils.byte_plus_256_do_not_wrap out hout

  rw [sub_eq_zero] at h
  apply eq_add_of_sub_eq at h
  rw [add_comm 256] at h
  apply_fun ZMod.val at h
  rw [not_wrap, out_plus_256_not_wrap] at h
  have h : (carry_in.val + x.val + y.val) - 256 = out.val :=
    Eq.symm (Nat.eq_sub_of_add_eq (Eq.symm h))

  -- reason about the bounds of the sum
  have sum_bound := FieldUtils.byte_sum_le_bound x y hx hy
  have sum_le_511 : carry_in.val + (x + y).val ≤ 511 := by
    apply Nat.le_sub_one_of_lt at sum_bound
    apply Nat.le_sub_one_of_lt at hb
    simp at sum_bound
    simp at hb
    apply Nat.add_le_add hb sum_bound
  rw [xy_not_wrap, ←add_assoc] at sum_le_511


  set x := x.val
  set y := y.val
  set carry_in := carry_in.val
  set out := out.val

  -- if the carry is one, then surely the sum does not fit in a byte
  have x_plus_y_overflow_byte : carry_in + x + y ≥ 256 := by
    have h2 : out + 256 >= 256 := by simp
    rw [←h] at h2
    linarith

  apply And.intro
  · have sub_mod := Nat.mod_eq_sub_mod x_plus_y_overflow_byte
    rw [←h] at hout
    rw [sub_mod, Nat.mod_eq_of_lt hout, h]
  · rw [Nat.div_eq_of_lt_le]
    · rw [←Nat.one_mul 256] at x_plus_y_overflow_byte; assumption
    · simp
      apply Nat.lt_add_one_of_le
      assumption

/--
  Soundness of the 8-bit addition circuit: assuming that the constraints and assumptions
  are satisfied, the output is correctly the sum of the inputs and the input
  carry modulo 256. Additionally the output carry is exactly the integer division
  of the aforementioned sum by 256.
-/
theorem soundness (x y out carry_in carry_out: F p):
    x.val < 256 -> y.val < 256 ->
    out.val < 256 ->
    (carry_in = 0 ∨ carry_in = 1) ->
    (carry_out = 0 ∨ carry_out = 1) ->
    (x + y + carry_in + -1 * out + -1 * (carry_out * 256) = 0) ->
    (out.val = (x.val + y.val + carry_in.val) % 256
    ∧ carry_out.val = (x.val + y.val + carry_in.val) / 256):= by
  intros hx hy hout carry_in_bool carry_out_bool h
  have carry_in_bound := FieldUtils.boolean_le_2 carry_in carry_in_bool

  rcases carry_out_bool with zero_carry | one_carry
  -- case with zero carry
  · rw [zero_carry] at h
    simp [ZMod.val_add] at h
    rw [←sub_eq_add_neg] at h
    have h_spec : carry_in + x + y - out = 0 := by
      rw [add_comm (x + y), ←add_assoc] at h
      assumption

    have thm := soundness_zero_carry x y out carry_in hx hy hout carry_in_bound h_spec
    apply_fun ZMod.val at zero_carry

    -- now it is just a matter of shuffling terms around
    have shuffle_terms : carry_in.val + x.val + y.val = x.val + y.val + carry_in.val := by
      zify; ring
    rw [ZMod.val_zero, ← thm.right] at zero_carry
    rw [shuffle_terms] at thm
    rw [shuffle_terms] at zero_carry
    constructor
    · exact thm.left
    · exact zero_carry

  -- case with one carry
  · rw [one_carry] at h
    simp [ZMod.val_add] at h
    -- rw [←sub_eq_add_neg, ←sub_eq_add_neg (carry_in + x + y)] at h
    have h_spec : carry_in + x + y - out - 256 = 0 := by
      rw [add_comm (x + y), ←add_assoc] at h
      ring_nf at h; ring_nf
      assumption

    -- instantiate the sub-theorem
    have thm := soundness_one_carry x y out carry_in hx hy hout carry_in_bound h_spec
    apply_fun ZMod.val at one_carry

    have shuffle_terms : carry_in.val + x.val + y.val = x.val + y.val + carry_in.val := by
      zify; ring
    rw [ZMod.val_one, ← thm.right] at one_carry
    rw [shuffle_terms] at thm
    rw [shuffle_terms] at one_carry
    constructor
    · exact thm.left
    · exact one_carry

/--
  Given the default witness generation, we show that the addition constraint is satisfied
-/
theorem completeness_add [p_neq_zero : Fact (p ≠ 0)] (x y carry_in: F p) :
    x.val < 256 ->
    y.val < 256 ->
    carry_in.val < 2 ->
    let carry_out := FieldUtils.floordiv (x + y + carry_in) 256
    let z := FieldUtils.mod_256 (x + y + carry_in)
    x + y + carry_in + -1 * z + -1 * (carry_out * 256) = 0 := by
  intro as_x as_y carry_in_bound
  simp
  rw [←sub_eq_add_neg, sub_eq_zero, add_eq_of_eq_sub]
  ring_nf
  dsimp [FieldUtils.mod_256, FieldUtils.mod]

  -- lift everything to the naturals
  apply_fun ZMod.val
  · simp [ZMod.val_add (FieldUtils.floordiv (x + y + carry_in) 256 * 256)]
    dsimp [FieldUtils.floordiv]
    rw [ZMod.val_mul, FieldUtils.val_of_nat_to_field_eq, FieldUtils.val_of_nat_to_field_eq]
    repeat rw [ZMod.val_add]
    simp

    -- we need to show that the sum does not wrap around
    set T := ZMod.val x + ZMod.val y + ZMod.val carry_in
    have T_not_wrap : T % p = T := by
      dsimp [T]
      rw [Nat.mod_eq_iff_lt p_neq_zero.elim]
      have sum_bound := FieldUtils.byte_sum_le_bound x y as_x as_y
      have sum_lt_512 : (x + y).val + carry_in.val ≤ 511 := by
        apply Nat.le_sub_one_of_lt at sum_bound
        apply Nat.le_sub_one_of_lt at carry_in_bound
        simp at sum_bound
        simp at carry_in_bound
        apply Nat.add_le_add sum_bound carry_in_bound
      have sum_lt_p : (x + y).val + carry_in.val < p := Nat.lt_trans
        (by apply Nat.lt_add_one_of_le at sum_lt_512; assumption) p_large_enough.elim
      rw [FieldUtils.byte_sum_do_not_wrap x y as_x as_y] at sum_lt_p
      assumption
    rw [T_not_wrap]

    -- now we just need to prove a simple result about euclidean division over T
    have obv : (256 : F p).val = 256 % p := ZMod.val_natCast _
    have h : T / 256 * (ZMod.val (256 : F p)) + T % 256 = T := by
      rw [mul_comm, obv]
      rw [(Nat.mod_eq_iff_lt (m:=256) p_neq_zero.elim).mpr
        (Nat.lt_trans (by norm_num) p_large_enough.elim), Nat.div_add_mod]

    rw [h, T_not_wrap]
  · apply ZMod.val_injective

/--
  Given the default witness generation, we show that the output carry
  is either 0 or 1
-/
theorem completeness_bool [p_neq_zero : Fact (p ≠ 0)] (x y carry_in: F p) :
    x.val < 256 ->
    y.val < 256 ->
    carry_in.val < 2 ->
    let carry_out := FieldUtils.floordiv (x + y + carry_in) 256
    carry_out = 0 ∨ carry_out = 1 := by
  intro as_x as_y carry_in_bound
  dsimp [FieldUtils.floordiv]

  -- we show that the carry_out is either 0 or 1 by explicitly
  -- constructing the two cases
  have carry? := Nat.lt_or_ge (x.val + y.val + carry_in.val) 256
  rcases carry? with sum_lt_256 | sum_ge_256
  · -- we want to show that the carry is 0
    apply Or.inl
    apply_fun ZMod.val
    · rw [FieldUtils.val_of_nat_to_field_eq]
      have h : (x + y + carry_in).val = x.val + y.val + carry_in.val := by
        rw [ZMod.val_add, ZMod.val_add x]
        simp
        rw [(Nat.mod_eq_iff_lt p_neq_zero.elim).mpr
          (Nat.lt_trans sum_lt_256 (by linarith [p_large_enough.elim]))]
      rw [h]
      rw [Nat.div_eq_of_lt sum_lt_256]
      simp
    · apply ZMod.val_injective
  · have sum_bound := FieldUtils.byte_sum_le_bound x y as_x as_y
    have sum_le_511 : (x + y).val + carry_in.val ≤ 511 := by
      apply Nat.le_sub_one_of_lt at sum_bound
      apply Nat.le_sub_one_of_lt at carry_in_bound
      simp at sum_bound
      simp at carry_in_bound
      rw [add_comm]
      apply Nat.add_le_add carry_in_bound sum_bound
    rw [FieldUtils.byte_sum_do_not_wrap x y as_x as_y] at sum_le_511

    -- we want to show that the carry is 1
    apply Or.inr
    apply_fun ZMod.val
    · rw [FieldUtils.val_of_nat_to_field_eq]
      have div_one : (x.val + y.val + carry_in.val) / 256 = 1 := by
        apply Nat.div_eq_of_lt_le
        · simp; apply sum_ge_256
        · simp; apply Nat.lt_add_one_of_le; apply sum_le_511
      rw [ZMod.val_one]
      rw [FieldUtils.byte_sum_and_bit_do_not_wrap' x y carry_in as_x as_y carry_in_bound]
      assumption
    · apply ZMod.val_injective

end Add8Theorems
