import Clean.Circuit.Basic
import Clean.Utils.Field

namespace Gadgets.Xor
open ByteUtils
variable {p : ℕ} [Fact p.Prime] [p_large_enough: Fact (p > 512)]

def ByteXorTable: Table (F p) where
  name := "ByteXor"
  length := 256*256
  arity := 3
  row i :=
    let (x, y) := split_two_bytes i
    #v[from_byte x, from_byte y, from_byte (x ^^^ y)]

def ByteXorLookup (x y z: Expression (F p)) : Lookup (F p) := {
  table := ByteXorTable
  entry := #v[x, y, z]
  index env := by
    let x := x.eval env |>.val
    let y := y.eval env |>.val
    dsimp only [ByteXorTable]
    exact x * 256 + y
}

def ByteXorTable.soundness (x y z: F p) :
    ByteXorTable.contains #v[x, y, z] →
    x.val < 256 ∧ y.val < 256 ∧ z.val = x.val ^^^ y.val := by
  dsimp [Table.contains]
  rintro ⟨ i, h: #v[x, y, z] = ByteXorTable.row i ⟩
  simp [ByteXorTable] at h
  simp only [ByteXorTable] at i

  rcases h with ⟨ hx, hy, hz ⟩

  constructor
  · rw [hx]
    apply from_byte_lt
  constructor
  · rw [hy]
    apply from_byte_lt

  rw [hx, hy, hz]
  repeat rw [from_byte, FieldUtils.val_of_nat_to_field_eq]
  simp only [HXor.hXor, Xor.xor, Fin.xor]
  rw [Nat.mod_eq_iff_lt (by norm_num)]
  apply Nat.xor_lt_two_pow (n:=8)
  exact (split_two_bytes i).1.is_lt
  exact (split_two_bytes i).2.is_lt

def ByteXorTable.completeness (x y z: F p) :
    x.val < 256 ∧ y.val < 256 ∧ z.val = x.val ^^^ y.val →
    ByteXorTable.contains #v[x, y, z] := by
  intro ⟨ hx, hy, h ⟩
  dsimp only [ByteXorTable, Table.contains]
  use concat_two_bytes ⟨ x.val, hx ⟩ ⟨ y.val, hy ⟩
  simp only [Vector.eq_mk, Array.mk.injEq, List.cons.injEq, and_true]
  rw [concat_split]
  simp [from_byte_eq, true_and, from_byte, FieldUtils.nat_to_field_of_val_eq_iff]
  apply FieldUtils.ext
  simp only [h, HXor.hXor, Xor.xor, Fin.xor, from_byte, FieldUtils.val_of_nat_to_field_eq]

def ByteXorTable.equiv (x y z: F p) :
    ByteXorTable.contains #v[x, y, z] ↔
    x.val < 256 ∧ y.val < 256 ∧ z.val = x.val ^^^ y.val :=
  ⟨ByteXorTable.soundness x y z, ByteXorTable.completeness x y z⟩

end Gadgets.Xor
