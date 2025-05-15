import Clean.Circuit.Basic
import Clean.Utils.Field

namespace Gadgets.TwoPowerLookup
variable {p : ℕ} [Fact (p ≠ 0)] [Fact p.Prime]
variable [p_large_enough: Fact (p > 512)]

def from_byte_limb {two_power : Fin 8} (x: Fin (2 ^ two_power.val)) : F p :=
  FieldUtils.nat_to_field x.val (by
    have two_power_small : 2^two_power.val < 2 ^ 8 := by
      apply Nat.pow_lt_pow_of_lt
      · simp only [Nat.one_lt_ofNat]
      · exact two_power.is_lt
    linarith [x.is_lt, p_large_enough.elim])

/--
  Family of tables that contains all the values of `F p` that are less than `2^two_power`
  where `two_power` is a (compile-time) parameter of the table.
-/
def ByteLessThanTwoPower (two_power : Fin 8) : Table (F p) where
  name := "ByteLessThanTwoPower"
  length := 2^two_power.val
  arity := 1
  row i := #v[from_byte_limb i]

def soundness (two_power : Fin 8) (x: F p) :
    (ByteLessThanTwoPower two_power).contains (#v[x]) → x.val < 2^two_power.val := by
  dsimp only [ByteLessThanTwoPower, Table.contains]
  rintro ⟨ i, h: #v[x] = #v[from_byte_limb i] ⟩
  have h' : x = from_byte_limb i := by repeat injection h with h
  rw [FieldUtils.nat_to_field_eq x h']
  exact i.is_lt

def completeness (two_power : Fin 8) (x: F p) :
    x.val < 2^two_power.val → (ByteLessThanTwoPower two_power).contains (#v[x]) := by
  intro h
  dsimp only [ByteLessThanTwoPower, Table.contains]
  use x.val
  simp only [from_byte_limb, Fin.val_natCast]
  ext1
  have h' : (x.val) % 2^two_power.val = x.val := by
    rw [Nat.mod_eq_iff_lt]; assumption; norm_num
  simp only [h', List.cons.injEq, and_true]
  simp [FieldUtils.nat_to_field_of_val_eq_iff]

def equiv (two_power : Fin 8) (x: F p) :
    (ByteLessThanTwoPower two_power).contains (#v[x]) ↔ x.val < 2^two_power.val :=
  ⟨soundness two_power x, completeness two_power x⟩

def lookup (two_power : Fin 8) (x: Expression (F p)) : Lookup (F p) := {
  table := ByteLessThanTwoPower two_power
  entry := #v[x]
  index := fun env =>
    let x := x.eval env |>.val
    if h : (x < 2^two_power.val)
    then ⟨x, h⟩
    else ⟨0, by show 0 < 2^two_power.val; norm_num⟩
}
end Gadgets.TwoPowerLookup
