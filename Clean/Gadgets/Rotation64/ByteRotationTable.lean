import Clean.Circuit.Basic
import Clean.Utils.Field
import Clean.Gadgets.Rotation64.Theorems

namespace Gadgets.Rotation64
variable {p : ℕ} [Fact (p ≠ 0)] [Fact p.Prime]
variable [p_large_enough: Fact (p > 512)]

open Bitwise (rot_right8)

def from_byte (x: Fin 256) : F p :=
  FieldUtils.nat_to_field x.val (by linarith [x.is_lt, p_large_enough.elim])

def ByteRotationTable (offset : Fin 8) : Table (F p) where
  name := "ByteRotation"
  length := 256
  arity := 2
  row i := #v[from_byte i, from_byte (rot_right8 i offset)]

def ByteRotationTable.soundness
    (offset : Fin 8)
    (x y: F p)
    (hx : x.val < 256) : -- TODO: is hx necessary?
    (ByteRotationTable offset).contains (#v[x, y]) → y.val = rot_right8 ⟨x.val, hx⟩ offset := by
  dsimp only [Table.contains]
  rintro ⟨ i, h: #v[x, y] = #v[from_byte i, from_byte (rot_right8 i offset)] ⟩
  have list_eq : [x, y] = [from_byte i, from_byte (rot_right8 i offset)] := by
    simp only [Vector.eq_mk, Array.mk.injEq, List.cons.injEq, and_true] at h
    simp only [List.cons.injEq, and_true]
    trivial
  have h_y : y = from_byte (rot_right8 i offset) := by
    injection list_eq with list_eq tail_eq
    injection tail_eq
  have h_x : ⟨x.val, hx⟩ = i := by
    have h : x = from_byte i := by injection list_eq with list_eq tail_eq
    simp [from_byte] at h
    apply_fun ZMod.val at h
    apply_fun Fin.val
    · simp only
      rw [h, FieldUtils.val_of_nat_to_field_eq]
    · apply Fin.val_injective
  rw [h_y, h_x]
  simp only [from_byte, Fin.cast_val_eq_self]
  rw [FieldUtils.val_of_nat_to_field_eq]

def ByteRotationTable.completeness
    (offset : Fin 8)
    (x y: F p)
    (hx : x.val < 256):
    y.val = rot_right8 ⟨x.val, hx⟩ offset → (ByteRotationTable offset).contains (#v[x, y]) := by
  intro h
  dsimp only [ByteRotationTable, Table.contains]
  use x.val
  simp only [from_byte, Vector.eq_mk, Array.mk.injEq, List.cons.injEq, and_true, Fin.val_cast_of_lt hx]

  have h_x' : x.val % 256 = x.val := by
    apply (Nat.mod_eq_iff_lt (by linarith)).mpr
    exact hx

  constructor
  · rw [FieldUtils.nat_to_field_of_val_eq_iff]
  · apply_fun ZMod.val
    · rw [h, FieldUtils.val_of_nat_to_field_eq]
      have h_x'' : (⟨x.val, hx⟩ : Fin 256) = ZMod.cast x := by
        apply_fun Fin.val
        · rw [← ZMod.natCast_val x, Fin.val_natCast]
          simp only [h_x']
        · apply Fin.val_injective
      rw [h_x'']
      simp only [ZMod.natCast_val]
    · apply ZMod.val_injective

def ByteRotationTable.equiv (offset : Fin 8) (x y: F p) (hx : x.val < 256) :
    (ByteRotationTable offset).contains (#v[x, y]) ↔ y.val = rot_right8 ⟨x.val, hx⟩ offset :=
  ⟨ByteRotationTable.soundness offset x y hx, ByteRotationTable.completeness offset x y hx⟩

def byte_rotation_lookup (offset : Fin 8) (x y: Expression (F p)) := lookup {
  table := ByteRotationTable offset
  entry := #v[x, y]
  -- to make this work, we need to pass an `eval` function to the callback!!
  index := fun env =>
    let x := x.eval env |>.val
    if h : (x < 256)
    then ⟨x, h⟩
    else ⟨0, by show 0 < 256; norm_num⟩
}

end Gadgets.Rotation64
