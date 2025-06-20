import Clean.Circuit.Basic
import Clean.Utils.Field

namespace Gadgets
variable {p : ℕ} [Fact (p ≠ 0)] [Fact p.Prime]
variable [p_large_enough: Fact (p > 512)]

def from_byte (x: Fin 256) : F p :=
  FieldUtils.nat_to_field x.val (by linarith [x.is_lt, p_large_enough.elim])

def ByteTable : Table (F p) := StaticTable.toTable {
  name := "Bytes"
  length := 256
  arity := 1
  row i := #v[from_byte i]
  index := fun ⟨⟨[x]⟩, _⟩ => x.val
  soundness := fun ⟨⟨[x]⟩, _⟩ => x.val < 256
  completeness := fun ⟨⟨[x]⟩, _⟩ => x.val < 256

  imply_soundness := by
    intro ⟨⟨[x]⟩, _⟩
    dsimp only [StaticTable.toTable, StaticTable.contains]
    rintro ⟨ i, h: #v[x] = #v[from_byte i] ⟩
    have h' : x = from_byte i := by injections h
    have h'' : x.val = i.val := FieldUtils.nat_to_field_eq x h'
    rw [h'']
    exact i.is_lt

  implied_by_completeness := by
    intro ⟨⟨[x]⟩, _⟩
    dsimp only [StaticTable.toTable, StaticTable.contains]
    rintro h
    use x.val
    simp only [from_byte, Fin.val_natCast]
    ext1
    have h' : (x.val) % 256 = x.val := by
      rw [Nat.mod_eq_iff_lt]; assumption; norm_num
    simp only [h', List.cons.injEq]
    simp [FieldUtils.nat_to_field_of_val_eq_iff]
}

def ByteTable.equiv (x: F p) : ByteTable.contains (#v[x]) ↔ x.val < 256 :=
  ⟨ByteTable.imply_soundness #v[x], ByteTable.implied_by_completeness #v[x]⟩

def ByteLookup (x: Expression (F p)) : Lookup (F p) where
  table := ByteTable
  entry := #v[x]
end Gadgets
