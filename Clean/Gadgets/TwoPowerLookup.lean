import Clean.Circuit.Basic
import Clean.Utils.Field

namespace Gadgets.TwoPowerLookup
variable {p : ℕ} [Fact (p ≠ 0)] [Fact p.Prime]
variable [p_large_enough: Fact (p > 512)]

def from_byte_limb {two_exponent : Fin 9} (x: Fin (2 ^ two_exponent.val)) : F p :=
  FieldUtils.nat_to_field x.val (by
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
def ByteLessThanTwoPower (two_exponent : Fin 9) : StaticTable (F p) where
  name := "ByteLessThanTwoPower"
  length := 2^two_exponent.val
  arity := 1
  row i := #v[from_byte_limb i]

def soundness (two_exponent : Fin 9) (x: F p) :
    (ByteLessThanTwoPower two_exponent).contains (#v[x]) → x.val < 2^two_exponent.val := by
  dsimp only [ByteLessThanTwoPower, StaticTable.contains]
  rintro ⟨ i, h: #v[x] = #v[from_byte_limb i] ⟩
  have h' : x = from_byte_limb i := by repeat injection h with h
  rw [FieldUtils.nat_to_field_eq x h']
  exact i.is_lt

def completeness (two_exponent : Fin 9) (x: F p) :
    x.val < 2^two_exponent.val → (ByteLessThanTwoPower two_exponent).contains (#v[x]) := by
  intro h
  dsimp only [ByteLessThanTwoPower, StaticTable.contains]
  use x.val
  simp only [from_byte_limb, Fin.val_natCast]
  ext1
  have h' : (x.val) % 2^two_exponent.val = x.val := by
    rw [Nat.mod_eq_iff_lt]; assumption; norm_num
  simp only [h', List.cons.injEq, and_true]
  simp [FieldUtils.nat_to_field_of_val_eq_iff]

def equiv (two_exponent : Fin 9) (x: F p) :
    (ByteLessThanTwoPower two_exponent).contains (#v[x]) ↔ x.val < 2^two_exponent.val :=
  ⟨soundness two_exponent x, completeness two_exponent x⟩

def lookup (two_exponent : Fin 9) (x: Expression (F p)) : StaticLookup (F p) := {
  table := ByteLessThanTwoPower two_exponent
  entry := #v[x]
  index := fun env =>
    let x := x.eval env |>.val
    if h : (x < 2^two_exponent.val)
    then ⟨x, h⟩
    else ⟨0, by show 0 < 2^two_exponent.val; norm_num⟩
}
end Gadgets.TwoPowerLookup
