import Midnight.SHA256.Tables
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic

/-! Bit semantics of the actual spread function used to generate Midnight's SHA
lookup table. All results are generic in the input size; no table enumeration or
native-evaluation axiom is used. -/

namespace Midnight.SHA256.Semantics

/-- Base-four recurrence of the existing executable table function, including zero. -/
theorem spread_unfold (n : Nat) : spread n = n % 2 + 4 * spread (n / 2) := by
  cases n with
  | zero => simp [spread]
  | succ n => rw [spread]

@[simp] theorem spread_zero : spread 0 = 0 := by simp [spread]

/-- Spreading a bounded word inserts a zero at each odd bit position. -/
theorem spread_lt {n width : Nat} (hn : n < 2 ^ width) : spread n < 2 ^ (2 * width) := by
  induction width generalizing n with
  | zero =>
    have : n = 0 := by simpa using hn
    subst n
    simp
  | succ width ih =>
    have hhalf : n / 2 < 2 ^ width := by rw [pow_succ] at hn; omega
    have hspread := ih hhalf
    have hbit := Nat.mod_lt n (by decide : 0 < 2)
    rw [spread_unfold, show 2 * (width + 1) = 2 * width + 2 by omega, pow_add]
    norm_num
    omega

/-- Every even-position bit is exactly the corresponding input bit. -/
theorem spread_testBit_even (n i : Nat) : (spread n).testBit (2 * i) = n.testBit i := by
  induction i generalizing n with
  | zero =>
    rw [spread_unfold]
    simp only [Nat.mul_zero, Nat.testBit_zero]
    simp [Nat.add_mod, Nat.mul_mod]
  | succ i ih =>
    rw [spread_unfold, Nat.add_comm]
    change (2 ^ 2 * spread (n / 2) + n % 2).testBit (2 * (i + 1)) = _
    rw [Nat.testBit_two_pow_mul_add _ (by omega : n % 2 < 2 ^ 2)]
    simp only [show ¬ 2 * (i + 1) < 2 by omega, ite_false,
      show 2 * (i + 1) - 2 = 2 * i by omega, ih, Nat.testBit_div_two]

/-- Odd positions are zero, so the expansion has no hidden payload bits. -/
theorem spread_testBit_odd (n i : Nat) : (spread n).testBit (2 * i + 1) = false := by
  induction i generalizing n with
  | zero =>
    rw [spread_unfold, Nat.add_comm]
    change (2 ^ 2 * spread (n / 2) + n % 2).testBit 1 = false
    rw [Nat.testBit_two_pow_mul_add _ (by omega : n % 2 < 2 ^ 2)]
    exact Nat.testBit_lt_two_pow (by simpa using Nat.mod_lt n (by decide : 0 < 2))
  | succ i ih =>
    rw [spread_unfold, Nat.add_comm]
    change (2 ^ 2 * spread (n / 2) + n % 2).testBit (2 * (i + 1) + 1) = _
    rw [Nat.testBit_two_pow_mul_add _ (by omega : n % 2 < 2 ^ 2)]
    simpa only [show ¬ 2 * (i + 1) + 1 < 2 by omega, ite_false,
      show 2 * (i + 1) + 1 - 2 = 2 * i + 1 by omega] using ih (n / 2)

/-- Characterization in both directions by the full bit-interleaving relation. -/
theorem eq_spread_iff (expanded plain : Nat) : expanded = spread plain ↔
    (∀ i, expanded.testBit (2 * i) = plain.testBit i) ∧
    (∀ i, expanded.testBit (2 * i + 1) = false) := by
  constructor
  · intro h; subst expanded
    exact ⟨spread_testBit_even plain, spread_testBit_odd plain⟩
  · rintro ⟨he, ho⟩
    apply Nat.eq_of_testBit_eq
    intro i
    have hi : i = 2 * (i / 2) + i % 2 := by omega
    rcases Nat.mod_two_eq_zero_or_one i with h | h
    · rw [hi, h, Nat.add_zero, he, spread_testBit_even]
    · rw [hi, h, ho, spread_testBit_odd]

/-- The recursive function agrees with binary digit construction. -/
theorem spread_bit (b : Bool) (n : Nat) :
    spread (Nat.bit b n) = b.toNat + 4 * spread n := by
  rw [spread_unfold]
  cases b <;> simp [Nat.bit, Nat.add_div]

/-- Concatenating bounded input limbs shifts their spread encodings by twice
as many bits, exactly as the native reconstruction gates do. -/
theorem spread_concat {lo : Nat} (width hi : Nat) (bound : lo < 2 ^ width) :
    spread (lo + 2 ^ width * hi) = spread lo + 2 ^ (2 * width) * spread hi := by
  induction width generalizing lo with
  | zero =>
    have : lo = 0 := by simpa using bound
    subst lo
    simp
  | succ width ih =>
    have hhalf : lo / 2 < 2 ^ width := by rw [pow_succ] at bound; omega
    have hshift : lo + 2 ^ (width + 1) * hi = lo + 2 * (2 ^ width * hi) := by ring
    have hdiv : (lo + 2 ^ (width + 1) * hi) / 2 = lo / 2 + 2 ^ width * hi := by
      rw [hshift]; simp [Nat.add_mul_div_left]
    have hmod : (lo + 2 ^ (width + 1) * hi) % 2 = lo % 2 := by
      rw [hshift]; omega
    rw [spread_unfold (lo + _), hdiv, hmod, ih hhalf, spread_unfold lo]
    rw [show 2 * (width + 1) = 2 * width + 2 by omega, pow_add]
    ring

end Midnight.SHA256.Semantics
