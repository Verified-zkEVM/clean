import Midnight.Field
import Clean.Gadgets.Boolean
import Mathlib.Tactic

/-! Bounded-integer consequences of Midnight's field equations. The bounds are
explicit: without them a field equation is only a congruence. Callers obtain
word and carry bounds from the actual decomposition and lookup constraints. -/

namespace Midnight.SHA256.Semantics

theorem nat_eq_of_field_eq {a b : Nat}
    (ha : a < BLS12_381.scalarFieldSize) (hb : b < BLS12_381.scalarFieldSize)
    (h : (a : F) = (b : F)) : a = b := by
  have heq := congrArg ZMod.val h
  simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using heq

/-- The carry lookup admits three bits. Together with a 32-bit result, both
sides of the addition gate are far below the scalar modulus. -/
theorem add32_gate_sound {sum result carry : Nat}
    (hsum : sum < 7 * 2 ^ 32) (hresult : result < 2 ^ 32) (hcarry : carry < 8)
    (hgate : (sum : F) - ((result : F) + (carry : F) * (2 ^ 32 : F)) = 0) :
    result = sum % 2 ^ 32 ∧ carry = sum / 2 ^ 32 := by
  have hfield : (sum : F) = ((result + carry * 2 ^ 32 : Nat) : F) := by
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using
      sub_eq_zero.mp hgate
  have hnat : sum = result + carry * 2 ^ 32 := nat_eq_of_field_eq
    (hsum.trans (by norm_num [BLS12_381.scalarFieldSize]))
    (by norm_num [BLS12_381.scalarFieldSize] at *; omega) hfield
  constructor <;> omega

/-- The honest carry and remainder satisfy the native gate, with no presumed
gate equation in the preconditions. -/
theorem add32_gate_complete (sum : Nat) :
    (sum : F) - ((sum % 2 ^ 32 : Nat) : F) -
      ((sum / 2 ^ 32 : Nat) : F) * (2 ^ 32 : F) = 0 := by
  have h := congrArg (fun n : Nat => (n : F)) (Nat.mod_add_div sum (2 ^ 32))
  push_cast at h
  linear_combination -h

/-- A gate booleanity equation establishes a genuine bit in the scalar field. -/
theorem bool_val_lt_two {value : F} (h : value * (value - 1) = 0) :
    value.val < 2 :=
  IsBool.val_lt_two (IsBool.iff_mul_sub_one.mpr h)

end Midnight.SHA256.Semantics
