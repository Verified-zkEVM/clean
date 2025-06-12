import Clean.Utils.Field
import Clean.Utils.Bitwise
import Clean.Types.U64
import Clean.Types.U32

namespace Gadgets.ByteDecomposition.Theorems
variable {p : ℕ} [Fact p.Prime] [p_large_enough: Fact (p > 2^16 + 2^8)]
instance : Fact (p > 512) := .mk (by linarith [p_large_enough.elim])

open FieldUtils (two_val two_pow_val)

theorem byte_decomposition_lift {x low high two_power : F p}
  (h_low : low.val < 2^8) (h_high : high.val < 2^8) (h_two_power : two_power.val ≤ 256)
  (h : x = low + high * two_power) :
    x.val = low.val + high.val * two_power.val := by
  rw [h]
  field_to_nat
  suffices high.val * two_power.val < 2^8 * 2^8 by linarith [p_large_enough.elim]
  apply Nat.mul_lt_mul_of_lt_of_le (by assumption) (by assumption)
  apply Nat.pow_pos
  trivial

theorem soundness (offset : Fin 8) (x low high : F p)
  (x_lt : x.val < 2^8) (low_lt : low.val < 2^offset.val) (high_lt : high.val < 2^8)
  (h_eq : x = low + high * 2^offset.val) :
    low.val = x.val % 2^offset.val ∧ high.val = x.val / 2^offset.val := by

  have two_power_lt : 2^offset.val < 2^8 := Nat.pow_lt_pow_of_lt (by linarith) offset.is_lt
  have two_power_val : ((2 : F p)^offset.val).val = 2^offset.val := two_pow_val offset.val (by linarith [offset.is_lt])
  have two_power_lt' : (2^offset.val : F p).val < 2^8 := by rwa [two_power_val]

  have low_byte : low.val < 256 := by linarith
  have h := byte_decomposition_lift low_byte high_lt (by linarith) h_eq
  rw [two_power_val] at h

  set low_b := UInt32.ofNat low.val
  set high_b := UInt32.ofNat high.val
  set x_b := UInt32.ofNat x.val

  -- The heavy lifting is done by using a SAT solver
  have h_decomposition_bv (base : UInt32) :
      base < 256 → low_b < base → high_b < 256 → x_b < 256 →
      x_b = low_b + high_b * base →
      low_b = x_b % base ∧ high_b = x_b / base := by
    bv_decide

  -- now it is left to prove that the bv variant is equivalent
  -- to the field variant of the theorem

  -- TODO: when updating to new Mathlib, all the following lemmas should be much easier to prove
  -- thanks new UInt32 lemmas
  have two_power_mod : (2^offset.val % 2 ^ 32) = 2^offset.val := by
    rw [Nat.mod_eq_iff_lt]
    linarith
    simp only [Nat.reducePow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, low_b, x_b]

  have two_power_lt_bv : UInt32.ofNat (2^offset.val) < 256 := by
    rw [UInt32.lt_iff_toNat_lt]
    simp only [UInt32.toNat_ofNat', Nat.reducePow, UInt32.toNat_ofNat, Nat.reduceMod]
    rw [Nat.mod_eq_of_lt (by linarith)]
    linarith

  have low_mod : low.val % 2^32 = low.val := by
    rw [Nat.mod_eq_iff_lt]
    linarith
    simp only [Nat.reducePow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, low_b, x_b]

  have high_mod : high.val % 2^32 = high.val := by
    rw [Nat.mod_eq_iff_lt]
    linarith
    simp only [Nat.reducePow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, low_b, x_b]

  have x_mod : x.val % 2^32 = x.val := by
    rw [Nat.mod_eq_iff_lt]
    linarith
    simp only [Nat.reducePow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, low_b, x_b]

  have low_b_lt : low_b < UInt32.ofNat (2^offset.val) := by
    simp only [low_b]
    rw [UInt32.lt_iff_toNat_lt]
    simp only [UInt32.toNat_ofNat', low_b]
    rw [low_mod, two_power_mod]
    assumption

  have high_b_lt : high_b < 256 := by
    simp only [high_b]
    rw [UInt32.lt_iff_toNat_lt]
    simp only [UInt32.toNat_ofNat', UInt32.toNat_div, UInt32.reduceToNat, low_b, high_b]
    rw [high_mod]
    assumption

  have x_lt : x_b < 256 := by
    simp only [x_b]
    rw [UInt32.lt_iff_toNat_lt]
    simp only [UInt32.toNat_ofNat', UInt32.reduceToNat, high_b, low_b, x_b]
    rw [x_mod]
    assumption

  have eq_holds_bv : x_b = low_b + high_b * UInt32.ofNat (2^offset.val) := by
    simp only [x_b, low_b, high_b]
    rw [←UInt32.toNat_inj]
    simp only [UInt32.toNat_ofNat', UInt32.toNat_add, UInt32.toNat_mul,
      Nat.mul_mod_mod, Nat.mod_mul_mod, Nat.add_mod_mod, Nat.mod_add_mod, high_b, low_b, x_b]
    rw [x_mod]
    have h : (low.val + high.val * (2^offset.val)) % 2^32 = low.val + high.val * (2^offset.val) := by
      apply Nat.mod_eq_of_lt
      linarith [p_large_enough.elim]
    rw [h]
    assumption

  specialize h_decomposition_bv (UInt32.ofNat (2^offset.val))
    two_power_lt_bv low_b_lt high_b_lt x_lt eq_holds_bv

  obtain ⟨h1, h2⟩ := h_decomposition_bv

  constructor
  · apply_fun UInt32.toNat at h1
    simp only [UInt32.toNat_ofNat', UInt32.toNat_mod, low_b, x_b] at h1
    rw [low_mod, x_mod, two_power_mod] at h1
    assumption
  · apply_fun UInt32.toNat at h2
    simp only [UInt32.toNat_ofNat', UInt32.toNat_div, high_b, x_b, low_b] at h2
    rw [high_mod, x_mod, two_power_mod] at h2
    assumption

end Gadgets.ByteDecomposition.Theorems
