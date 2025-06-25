import Clean.Circuit.Basic
import Clean.Utils.Field

namespace Gadgets
variable {p : ℕ} [Fact (p ≠ 0)] [Fact p.Prime]
variable [p_large_enough: Fact (p > 512)]

def fromByte (x: Fin 256) : F p :=
  FieldUtils.nat_to_field x.val (by linarith [x.is_lt, p_large_enough.elim])

def ByteTable : Table (F p) field := .fromStatic {
  name := "Bytes"
  length := 256

  row i := fromByte i
  index x := x.val

  Spec x := x.val < 256

  contains_iff := by
    intro x
    constructor
    · intro ⟨ i, h ⟩
      have h'' : x.val = i.val := FieldUtils.nat_to_field_eq x h
      rw [h'']
      exact i.is_lt
    · intro h
      use x.val
      simp only [fromByte, Fin.val_natCast]
      have h' : (x.val) % 256 = x.val := by
        rw [Nat.mod_eq_iff_lt]; assumption; norm_num
      simp only [h', List.cons.injEq]
      simp [FieldUtils.nat_to_field_of_val_eq_iff]
}
end Gadgets
