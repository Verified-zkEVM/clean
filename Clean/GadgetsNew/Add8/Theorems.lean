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

end Add8Theorems