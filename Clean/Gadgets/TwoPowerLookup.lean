import Clean.Circuit.Basic
import Clean.Utils.Field

namespace Gadgets.TwoPowerLookup
variable {p : ℕ} [Fact (p ≠ 0)] [Fact p.Prime]
variable [p_large_enough: Fact (p > 512)]

def from_byte_limb {two_exponent : Fin 9} (x: Fin (2 ^ two_exponent.val)) : F p :=
  FieldUtils.natToField x.val (by
    have two_exponent_small : 2^two_exponent.val < 2 ^ 9 := by
      apply Nat.pow_lt_pow_of_lt
      · simp only [Nat.one_lt_ofNat]
      · exact two_exponent.is_lt
    linarith [x.is_lt, p_large_enough.elim])

/--
  Family of tables that contains all the values of `F p` that are less than `2^two_exponent`
  where `two_exponent` is a (compile-time) parameter of the table.
  Supports `two_exponent` values from `0` to `8` included.
-/
def ByteLessThanTwoPower (two_exponent : Fin 9) : Table (F p) field := .fromStatic {
  name := "ByteLessThanTwoPower"
  length := 2^two_exponent.val

  row i := from_byte_limb i
  index x := x.val

  Spec x := x.val < 2^two_exponent.val

  contains_iff x := by
    constructor
    · dsimp only
      rintro ⟨ i, h ⟩
      rw [FieldUtils.natToField_eq x h]
      exact i.is_lt
    · dsimp only
      rintro h
      use x.val
      simp only [from_byte_limb, Fin.val_natCast]
      have h' : (x.val) % 2^two_exponent.val = x.val := by
        rw [Nat.mod_eq_iff_lt]; assumption; norm_num
      simp only [h', List.cons.injEq, and_true]
      simp [FieldUtils.natToField_of_val_eq_iff]
}
end Gadgets.TwoPowerLookup
