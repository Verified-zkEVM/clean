import Clean.Gadgets.Addition8.Addition8FullCarry
import Clean.Types.U32
import Clean.Utils.Field

variable {p : ℕ} [Fact p.Prime]
variable [p_large_enough: Fact (p > 512)]

namespace Gadgets.Addition32.Theorems

lemma lift_val1 {x y b : (F p)} (x_byte : x.val < 256) (y_byte : y.val < 256) (b_bool : b = 0 ∨ b = 1) :
    (x + y + b).val = (x.val + y.val + b.val) := by
  calc (x + y + b).val
  _ = (b + x + y).val := by ring_nf
  _ = b.val + x.val + y.val := by
    rw [FieldUtils.byte_sum_and_bit_do_not_wrap _ _ _ x_byte y_byte]
    apply FieldUtils.boolean_lt_2
    exact b_bool
  _ = x.val + y.val + b.val := by ring

lemma lift_val2 {x b : (F p)} (x_byte : x.val < 256) (b_bool : b = 0 ∨ b = 1) :
    (b * 256 + x).val = (b.val * 256 + x.val) := by
  rcases b_bool with b_zero | b_one
  · rw [b_zero]
    simp only [zero_mul, zero_add, ZMod.val_zero]
  · rw [b_one, ZMod.val_one]
    simp
    rw [add_comm 256 _]
    rw [FieldUtils.byte_plus_256_do_not_wrap]
    rw [add_comm]
    assumption

omit p_large_enough in
lemma zify_bool {b : (F p)} (b_bool : b = 0 ∨ b = 1) : (↑(b.val) : ℤ) = 0 ∨ (↑(b.val) : ℤ) = 1  := by
  rcases b_bool with b_zero | b_one
  · rw [b_zero]
    simp only [ZMod.val_zero, CharP.cast_eq_zero, zero_ne_one, or_false]
  · rw [b_one, ZMod.val_one]
    simp only [Nat.cast_one, one_ne_zero, or_true]


theorem add32_soundness {x0 x1 x2 x3 y0 y1 y2 y3 carry_in c0 c1 c2 c3 z0 z1 z2 z3 : F p}
    (x0_byte : x0.val < 256) (x1_byte : x1.val < 256) (x2_byte : x2.val < 256) (x3_byte : x3.val < 256)
    (y0_byte : y0.val < 256) (y1_byte : y1.val < 256) (y2_byte : y2.val < 256) (y3_byte : y3.val < 256)
    (z0_byte : z0.val < 256) (z1_byte : z1.val < 256) (z2_byte : z2.val < 256) (z3_byte : z3.val < 256)
    (carry_in_bool : carry_in = 0 ∨ carry_in = 1) (c0_bool : c0 = 0 ∨ c0 = 1)
    (c1_bool : c1 = 0 ∨ c1 = 1) (c2_bool : c2 = 0 ∨ c2 = 1) (c3_bool : c3 = 0 ∨ c3 = 1)
    (h0 : x0 + y0 + carry_in = c0 * 256 + z0)
    (h1 : x1 + y1 + c0 = c1 * 256 + z1)
    (h2 : x2 + y2 + c1 = c2 * 256 + z2)
    (h3 : x3 + y3 + c2 = c3 * 256 + z3) :
    ZMod.val z0 + ZMod.val z1 * 256 + ZMod.val z2 * 256 ^ 2 + ZMod.val z3 * 256 ^ 3 =
      (ZMod.val x0 + ZMod.val x1 * 256 + ZMod.val x2 * 256 ^ 2 + ZMod.val x3 * 256 ^ 3 +
            (ZMod.val y0 + ZMod.val y1 * 256 + ZMod.val y2 * 256 ^ 2 + ZMod.val y3 * 256 ^ 3) +
          ZMod.val carry_in) %
        2 ^ 32 ∧
    ZMod.val c3 =
      (ZMod.val x0 + ZMod.val x1 * 256 + ZMod.val x2 * 256 ^ 2 + ZMod.val x3 * 256 ^ 3 +
            (ZMod.val y0 + ZMod.val y1 * 256 + ZMod.val y2 * 256 ^ 2 + ZMod.val y3 * 256 ^ 3) +
          ZMod.val carry_in) /
        2 ^ 32
  := by

  apply_fun ZMod.val at h0 h1 h2 h3
  rw [lift_val1 x0_byte y0_byte carry_in_bool, lift_val2 z0_byte c0_bool] at h0
  rw [lift_val1 x1_byte y1_byte c0_bool, lift_val2 z1_byte c1_bool] at h1
  rw [lift_val1 x2_byte y2_byte c1_bool, lift_val2 z2_byte c2_bool] at h2
  rw [lift_val1 x3_byte y3_byte c2_bool, lift_val2 z3_byte c3_bool] at h3

  have c0_bool := zify_bool c0_bool
  have c1_bool := zify_bool c1_bool
  have c2_bool := zify_bool c2_bool
  have c3_bool := zify_bool c3_bool
  have carry_in_bool := zify_bool carry_in_bool

  have x0_pos : 0 ≤ x0.val := by exact Nat.zero_le _
  have y0_pos : 0 ≤ y0.val := by exact Nat.zero_le _
  have x1_pos : 0 ≤ x1.val := by exact Nat.zero_le _
  have y1_pos : 0 ≤ y1.val := by exact Nat.zero_le _
  have x2_pos : 0 ≤ x2.val := by exact Nat.zero_le _
  have y2_pos : 0 ≤ y2.val := by exact Nat.zero_le _
  have x3_pos : 0 ≤ x3.val := by exact Nat.zero_le _
  have y3_pos : 0 ≤ y3.val := by exact Nat.zero_le _
  have z0_pos : 0 ≤ z0.val := by exact Nat.zero_le _
  have z1_pos : 0 ≤ z1.val := by exact Nat.zero_le _
  have z2_pos : 0 ≤ z2.val := by exact Nat.zero_le _
  have z3_pos : 0 ≤ z3.val := by exact Nat.zero_le _

  zify at *

  set x0 : ℤ := ↑(ZMod.val x0)
  set x1 : ℤ := ↑(ZMod.val x1)
  set x2 : ℤ := ↑(ZMod.val x2)
  set x3 : ℤ := ↑(ZMod.val x3)
  set y0 : ℤ := ↑(ZMod.val y0)
  set y1 : ℤ := ↑(ZMod.val y1)
  set y2 : ℤ := ↑(ZMod.val y2)
  set y3 : ℤ := ↑(ZMod.val y3)
  set z0 : ℤ := ↑(ZMod.val z0)
  set z1 : ℤ := ↑(ZMod.val z1)
  set z2 : ℤ := ↑(ZMod.val z2)
  set z3 : ℤ := ↑(ZMod.val z3)
  set c0 : ℤ := ↑(ZMod.val c0)
  set c1 : ℤ := ↑(ZMod.val c1)
  set c2 : ℤ := ↑(ZMod.val c2)
  set c3 : ℤ := ↑(ZMod.val c3)
  set carry_in : ℤ := ↑(ZMod.val carry_in)

  -- now everything, assumptions and goal, is over Z

  -- add up all the equations
  set z := z0 + z1*256 + z2*256^2 + z3*256^3
  set x := x0 + x1*256 + x2*256^2 + x3*256^3
  set y := y0 + y1*256 + y2*256^2 + y3*256^3
  let lhs := z + c3*2^32
  let rhs₀ := x0 + y0 + carry_in + -1 * z0 + -1 * (c0 * 256) -- h0 expression
  let rhs₁ := x1 + y1 + c0 + -1 * z1 + -1 * (c1 * 256) -- h1 expression
  let rhs₂ := x2 + y2 + c1 + -1 * z2 + -1 * (c2 * 256) -- h2 expression
  let rhs₃ := x3 + y3 + c2 + -1 * z3 + -1 * (c3 * 256) -- h3 expression

  have h_add := calc z + c3*2^32
    -- substitute equations
    _ = lhs + 0 + 256*0 + 256^2*0 + 256^3*0 := by ring
    _ = lhs + rhs₀ + 256*rhs₁ + 256^2*rhs₂ + 256^3*rhs₃ := by
      simp only [rhs₀, rhs₁, rhs₂, rhs₃]
      simp only [h0, h1, h2, h3]
      ring
    -- simplify
    _ = x + y + carry_in := by ring


  have z_lt_2_32 : z < 2^32 := by dsimp only [z]; linarith
  have z_pos : 0 ≤ z := by dsimp [z]; linarith

  rcases c3_bool with c3_zero | c3_one
  · rw [c3_zero] at h_add
    simp only [Int.reducePow, zero_mul, add_zero] at h_add
    have sum_pos : 0 ≤ x + y + carry_in := by
      rcases carry_in_bool with c_zero | c_one
      · rw [c_zero]; linarith
      · rw [c_one]; linarith
    rw [Int.emod_eq_of_lt sum_pos (by linarith)]
    rw [Int.ediv_eq_zero_of_lt sum_pos (by linarith)]
    simp only [h_add, c3_zero, and_self]
  · simp only [c3_one, one_mul] at h_add
    rw [←h_add, Int.add_emod_self, Int.emod_eq_of_lt z_pos (by linarith)]
    rw [
      show z + 2^32 = z + 2^32 * 1 from rfl,
      Int.add_mul_ediv_left _ _ (by linarith),
      Int.ediv_eq_zero_of_lt z_pos z_lt_2_32
    ]
    simp only [c3_one, zero_add, and_self]
