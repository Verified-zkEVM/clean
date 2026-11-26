import Midnight.SHA256.Semantics.Spread
import Midnight.SHA256.Semantics.Field
import Clean.Specs.SHA256
import CompPoly.Data.Nat.Bitwise

/-! Natural-number semantics of the parity equations used by Midnight SHA.
These results infer bitwise outputs from a satisfied equation, independently
of the witness-generation algorithm. -/

namespace Midnight.SHA256.Semantics

/-- Addition of two spread words exposes XOR in even positions and AND in odd
positions. The identity holds over naturals, before any field cast. -/
theorem spread_add_two (a b : Nat) :
    spread a + spread b = spread (a ^^^ b) + 2 * spread (a &&& b) := by
  induction a using Nat.binaryRec generalizing b with
  | zero => simp
  | bit ba a ih =>
    induction b using Nat.binaryRec with
    | zero => simp
    | bit bb b _ =>
      rw [Nat.xor_bit, Nat.land_bit]
      simp only [spread_bit]
      have h := ih b
      cases ba <;> cases bb <;> simp at h ⊢ <;> omega

/-- Three spread words expose the three-way XOR and majority, with no carry
between adjacent base-four digits. This is the integer identity behind the
native Maj and sigma spread equations. -/
theorem spread_add_three (a b c : Nat) :
    spread a + spread b + spread c =
      spread (a ^^^ b ^^^ c) + 2 * spread (Specs.SHA256.Maj a b c) := by
  induction a using Nat.binaryRec generalizing b c with
  | zero => simpa [Specs.SHA256.Maj] using spread_add_two b c
  | bit ba a ih =>
    induction b using Nat.binaryRec with
    | zero => simpa [Specs.SHA256.Maj] using spread_add_two (Nat.bit ba a) c
    | bit bb b _ =>
      induction c using Nat.binaryRec with
      | zero => simpa [Specs.SHA256.Maj] using spread_add_two (Nat.bit ba a) (Nat.bit bb b)
      | bit bc c _ =>
        simp only [Specs.SHA256.Maj, Nat.xor_bit, Nat.land_bit, spread_bit]
        have h := ih b c
        cases ba <;> cases bb <;> cases bc <;>
          simp [Specs.SHA256.Maj] at h ⊢ <;> omega

/-- Packed even and odd bit planes. -/
def interleave (even odd : Nat) : Nat := spread even + 2 * spread odd

theorem interleave_unfold (a b : Nat) :
    interleave a b = a % 2 + 2 * (b % 2) + 4 * interleave (a / 2) (b / 2) := by
  unfold interleave
  rw [spread_unfold a, spread_unfold b]
  ring

theorem interleave_testBit_even (a b i : Nat) :
    (interleave a b).testBit (2 * i) = a.testBit i := by
  induction i generalizing a b with
  | zero =>
    rw [interleave_unfold]
    simp [Nat.testBit_zero, Nat.add_mod, Nat.mul_mod]
  | succ i ih =>
    rw [interleave_unfold, Nat.add_comm]
    change (2 ^ 2 * interleave (a / 2) (b / 2) + (a % 2 + 2 * (b % 2))).testBit
      (2 * (i + 1)) = _
    rw [Nat.testBit_two_pow_mul_add _ (by omega : a % 2 + 2 * (b % 2) < 2 ^ 2)]
    simp only [show ¬ 2 * (i + 1) < 2 by omega, ite_false,
      show 2 * (i + 1) - 2 = 2 * i by omega, ih, Nat.testBit_div_two]

theorem interleave_testBit_odd (a b i : Nat) :
    (interleave a b).testBit (2 * i + 1) = b.testBit i := by
  induction i generalizing a b with
  | zero =>
    rw [interleave_unfold]
    simp only [Nat.mul_zero, Nat.zero_add, Nat.testBit_eq_decide_div_mod_eq, pow_one, pow_zero, Nat.div_one]
    congr 1
    apply propext
    omega
  | succ i ih =>
    rw [interleave_unfold, Nat.add_comm]
    change (2 ^ 2 * interleave (a / 2) (b / 2) + (a % 2 + 2 * (b % 2))).testBit
      (2 * (i + 1) + 1) = _
    rw [Nat.testBit_two_pow_mul_add _ (by omega : a % 2 + 2 * (b % 2) < 2 ^ 2)]
    simp only [show ¬ 2 * (i + 1) + 1 < 2 by omega, ite_false,
      show 2 * (i + 1) + 1 - 2 = 2 * i + 1 by omega, ih, Nat.testBit_div_two]

/-- A parity equation cannot swap or hide either output bit plane. -/
theorem interleave_injective {a b c d : Nat} (h : interleave a b = interleave c d) :
    a = c ∧ b = d := by
  constructor
  · apply Nat.eq_of_testBit_eq
    intro i
    rw [← interleave_testBit_even a b i, h, interleave_testBit_even]
  · apply Nat.eq_of_testBit_eq
    intro i
    rw [← interleave_testBit_odd a b i, h, interleave_testBit_odd]

theorem spread_pair_sound {a b even odd : Nat}
    (equation : spread a + spread b = spread even + 2 * spread odd) :
    even = a ^^^ b ∧ odd = a &&& b := by
  apply interleave_injective
  exact equation.symm.trans (spread_add_two a b)

theorem spread_triple_sound {a b c even odd : Nat}
    (equation : spread a + spread b + spread c = spread even + 2 * spread odd) :
    even = a ^^^ b ^^^ c ∧ odd = Specs.SHA256.Maj a b c := by
  apply interleave_injective
  exact equation.symm.trans (spread_add_three a b c)

/-- Bounded-word complement, using exactly the finite XOR mask of SHA. -/
def complement (width a : Nat) : Nat := a ^^^ (2 ^ width - 1)

theorem and_complement_eq_zero {a width : Nat} (ha : a < 2 ^ width) :
    a &&& complement width a = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < width
  · simp only [complement, Nat.testBit_and, Nat.testBit_xor,
      Nat.testBit_two_pow_sub_one, hi, decide_true, Nat.zero_testBit]
    cases a.testBit i <;> rfl
  · have hbit : a.testBit i = false := Nat.testBit_lt_two_pow
      (ha.trans_le (Nat.pow_le_pow_right (by decide) (by omega)))
    simp [Nat.testBit_and, hbit]

theorem spread_complement {a width : Nat} (ha : a < 2 ^ width) :
    spread a + spread (complement width a) = spread (2 ^ width - 1) := by
  rw [spread_add_two, and_complement_eq_zero ha]
  simp [complement, Nat.xor_xor_cancel_left]

theorem complement_lt {a width : Nat} (ha : a < 2 ^ width) :
    complement width a < 2 ^ width := by
  apply Nat.xor_lt_two_pow ha
  exact Nat.sub_lt (by positivity) (by decide)

/-- The field subtraction used for the negated spread word is the finite
bitwise complement, provided the original word is bounded. -/
theorem spread_complement_field {a width : Nat} (ha : a < 2 ^ width) :
    (spread (complement width a) : F) =
      (spread (2 ^ width - 1) : F) - (spread a : F) := by
  have h := congrArg (fun n : Nat => (n : F)) (spread_complement ha)
  push_cast at h
  linear_combination h

/-- The concrete mask appearing in Midnight's SHA negation arithmetic. -/
theorem spread_mask32 : spread (2 ^ 32 - 1) = 0x5555555555555555 := by norm_num [spread]

/-- A pair of complementary AND terms has no overlapping carry bits. -/
theorem choice_terms_disjoint {a width : Nat} (ha : a < 2 ^ width) (b c : Nat) :
    (a &&& b) &&& (complement width a &&& c) = 0 := by
  have h := and_complement_eq_zero ha
  apply Nat.eq_of_testBit_eq
  intro i
  have hb := congrArg (fun n : Nat => n.testBit i) h
  simp only [Nat.testBit_and, Nat.zero_testBit] at hb ⊢
  cases hba : a.testBit i <;> cases hca : (complement width a).testBit i <;>
    simp [hba, hca] at hb ⊢

/-- The native addition of the two half-Ch outputs is SHA's XOR of disjoint
AND terms; this is an integer equality, not addition modulo the scalar field. -/
theorem choice_add_eq_xor {a width : Nat} (ha : a < 2 ^ width) (b c : Nat) :
    (a &&& b) + (complement width a &&& c) =
      (a &&& b) ^^^ (complement width a &&& c) := by
  rw [Nat.sum_eq_xor_plus_twice_and, choice_terms_disjoint ha]
  simp

/-- Soundness of the two-input native spread equation over the actual field.
Explicit word bounds rule out modular wraparound on either side. -/
theorem spread_pair_field_sound {a b even odd width : Nat}
    (ha : a < 2 ^ width) (hb : b < 2 ^ width)
    (he : even < 2 ^ width) (ho : odd < 2 ^ width)
    (capacity : 3 * 2 ^ (2 * width) ≤ BLS12_381.scalarFieldSize)
    (equation : (spread a : F) + (spread b : F) =
      (spread even : F) + 2 * (spread odd : F)) :
    even = a ^^^ b ∧ odd = a &&& b := by
  have sa := spread_lt ha
  have sb := spread_lt hb
  have se := spread_lt he
  have so := spread_lt ho
  apply spread_pair_sound
  apply nat_eq_of_field_eq (by omega) (by omega)
  simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using equation

/-- Soundness of the three-input native Maj/sigma parity equation over the
actual field, independently of how the output witness was generated. -/
theorem spread_triple_field_sound {a b c even odd width : Nat}
    (ha : a < 2 ^ width) (hb : b < 2 ^ width) (hc : c < 2 ^ width)
    (he : even < 2 ^ width) (ho : odd < 2 ^ width)
    (capacity : 3 * 2 ^ (2 * width) ≤ BLS12_381.scalarFieldSize)
    (equation : (spread a : F) + (spread b : F) + (spread c : F) =
      (spread even : F) + 2 * (spread odd : F)) :
    even = a ^^^ b ^^^ c ∧ odd = Specs.SHA256.Maj a b c := by
  have sa := spread_lt ha
  have sb := spread_lt hb
  have sc := spread_lt hc
  have se := spread_lt he
  have so := spread_lt ho
  apply spread_triple_sound
  apply nat_eq_of_field_eq (by omega) (by omega)
  simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using equation

/-- The field has ample capacity for all 32-bit SHA parity equations. -/
theorem sha256_parity_capacity :
    3 * 2 ^ (2 * 32) ≤ BLS12_381.scalarFieldSize := by
  norm_num [BLS12_381.scalarFieldSize]

end Midnight.SHA256.Semantics
