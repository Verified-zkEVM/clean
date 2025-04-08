import Clean.Circuit.Basic
import Clean.Utils.Field
import Clean.Gadgets.Rotation64.Theorems

namespace Gadgets.Xor
variable {p : ℕ} [Fact (p ≠ 0)] [Fact p.Prime]
variable [p_large_enough: Fact (p > 512)]

def from_byte (x: Fin 256) : F p :=
  FieldUtils.nat_to_field x.val (by linarith [x.is_lt, p_large_enough.elim])

omit [Fact (p ≠ 0)] in
lemma from_byte_lt (x: Fin 256) : (from_byte (p:=p) x).val < 256 := by
  dsimp [from_byte]
  rw [FieldUtils.val_of_nat_to_field_eq]
  exact x.is_lt

omit [Fact (p ≠ 0)] in
lemma from_byte_eq (x : F p) (x_lt : x.val < 256) : from_byte ⟨ x.val, x_lt ⟩ = x := by
  dsimp [from_byte]
  apply FieldUtils.nat_to_field_of_val_eq_iff

omit [Fact (p ≠ 0)] in
lemma from_byte_cast_eq {z: F p} (z_lt : z.val < 256) : from_byte z.cast = z := by
  simp only [from_byte]
  have : (z.cast : Fin 256).val = z.val := ZMod.val_cast_eq_val_of_lt z_lt
  simp only [this]
  apply FieldUtils.nat_to_field_of_val_eq_iff

def split_two_bytes (i : Fin (256 * 256)) : (Fin 256 × Fin 256) :=
  let x := i.val / 256
  let y := i.val % 256
  have x_lt : x < 256 := by simp [x, Nat.div_lt_iff_lt_mul]
  have y_lt : y < 256 := Nat.mod_lt i.val (by norm_num)
  (⟨ x, x_lt ⟩, ⟨ y, y_lt ⟩)

def concat_two_bytes (x y : Fin 256) : Fin (256 * 256) :=
  let i := x.val * 256 + y.val
  have i_lt : i < 256 * 256 := by
    unfold i
    linarith [x.is_lt, y.is_lt]
  ⟨ i, i_lt ⟩

lemma concat_split (x y : Fin 256) : split_two_bytes (concat_two_bytes x y) = (x, y) := by
  dsimp [split_two_bytes, concat_two_bytes]
  ext
  simp only
  rw [mul_comm]
  have h := Nat.mul_add_div (by norm_num : 256 > 0) x.val y.val
  rw [h]
  simp
  simp only [Nat.mul_add_mod_of_lt y.is_lt]

def ByteXorTable: Table (F p) where
  name := "ByteXor"
  length := 256*256
  arity := 3
  row i :=
    let (x, y) := split_two_bytes i
    #v[from_byte x, from_byte y, from_byte (Nat.xor x y)]

def ByteXorTable.soundness
    (x y z: F p) :
    ByteXorTable.contains #v[x, y, z] →
    x.val < 256 ∧ y.val < 256 ∧ z.val = Nat.xor x.val y.val := by
  dsimp [Table.contains]
  rintro ⟨ i, h: #v[x, y, z] = ByteXorTable.row i ⟩
  simp [ByteXorTable] at h
  simp only [ByteXorTable] at i
  dsimp [split_two_bytes] at i

  rcases h with ⟨ hx, hy, hz ⟩

  constructor
  · rw [hx]
    apply from_byte_lt
  constructor
  · rw [hy]
    apply from_byte_lt

  rw [hx, hy, hz]
  repeat rw [from_byte, FieldUtils.val_of_nat_to_field_eq]
  simp only [Fin.val_natCast, Nat.mod_succ_eq_iff_lt,
    Nat.succ_eq_add_one, Nat.reduceAdd]
  apply Nat.xor_lt_two_pow (n:=8)
  exact (split_two_bytes i).1.is_lt
  exact (split_two_bytes i).2.is_lt

def ByteXorTable.completeness
    (x y z: F p) :
    x.val < 256 ∧ y.val < 256 ∧ z.val = Nat.xor x.val y.val →
    ByteXorTable.contains #v[x, y, z] := by
  intro ⟨ hx, hy, h ⟩
  dsimp only [ByteXorTable, Table.contains]
  use concat_two_bytes ⟨ x.val, hx ⟩ ⟨ y.val, hy ⟩
  simp only [Vector.eq_mk, Array.mk.injEq, List.cons.injEq, and_true]
  rw [concat_split]
  simp only [from_byte_eq, true_and]
  have hz : z.val < 256 := h ▸ Nat.xor_lt_two_pow (n:=8) hx hy
  rw [←h]
  simp only [ZMod.natCast_val]
  rw [from_byte_cast_eq hz]

def ByteXorTable.equiv (x y z: F p) :
    ByteXorTable.contains #v[x, y, z] ↔
    x.val < 256 ∧ y.val < 256 ∧ z.val = Nat.xor x.val y.val :=
  ⟨ByteXorTable.soundness x y z, ByteXorTable.completeness x y z⟩

def byte_xor_lookup (x y z: Expression (F p)) := lookup {
  table := ByteXorTable
  entry := #v[x, y, z]
  index := fun env =>
    by
      let x := x.eval env |>.val
      let y := y.eval env |>.val
      dsimp [ByteXorTable]
      exact x * 256 + y
}

end Gadgets.Xor
