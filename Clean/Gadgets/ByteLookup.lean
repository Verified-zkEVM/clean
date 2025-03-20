import Clean.Circuit.Basic
import Clean.Utils.Field

section
variable {p : ℕ} [Fact (p ≠ 0)] [Fact p.Prime]
variable [p_large_enough: Fact (p > 512)]

def from_byte (x: Fin 256) : F p :=
  FieldUtils.nat_to_field x.val (by linarith [x.is_lt, p_large_enough.elim])

def ByteTable : Table (F p) where
  name := "Bytes"
  length := 256
  arity := 1
  row i := #v[from_byte i]

def ByteTable.soundness (x: F p) : ByteTable.contains (#v[x]) → x.val < 256 := by
  dsimp only [ByteTable, Table.contains]
  rintro ⟨ i, h: #v[x] = #v[from_byte i] ⟩
  have h' : x = from_byte i := by repeat injection h with h
  have h'' : x.val = i.val := FieldUtils.nat_to_field_eq x h'
  rw [h'']
  exact i.is_lt

def ByteTable.completeness (x: F p) : x.val < 256 → ByteTable.contains (#v[x]) := by
  intro h
  dsimp only [ByteTable, Table.contains]
  use x.val
  simp only [from_byte, Fin.val_natCast]
  ext1
  have h' : (x.val) % 256 = x.val := by
    rw [Nat.mod_eq_iff_lt]; assumption; norm_num
  simp only [h', List.cons.injEq, and_true]
  simp [FieldUtils.nat_to_field_of_val_eq_iff]

def ByteTable.equiv (x: F p) : ByteTable.contains (#v[x]) ↔ x.val < 256 :=
  ⟨ByteTable.soundness x, ByteTable.completeness x⟩

def byte_lookup (x: Expression (F p)) := lookup {
  table := ByteTable
  entry := #v[x]
  -- to make this work, we need to pass an `eval` function to the callback!!
  index := fun env =>
    let x := x.eval env |>.val
    if h : (x < 256)
    then ⟨x, h⟩
    else ⟨0, by show 0 < 256; norm_num⟩
}
end
