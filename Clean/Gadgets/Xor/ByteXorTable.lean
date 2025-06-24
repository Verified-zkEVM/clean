import Clean.Circuit.Basic
import Clean.Utils.Field

namespace Gadgets.Xor
open ByteUtils
variable {p : ℕ} [Fact p.Prime] [p_large_enough: Fact (p > 512)]

def ByteXorTable : Table (F p) fieldTriple := .fromStatic {
  name := "ByteXor"
  length := 256*256

  row i :=
    let (x, y) := split_two_bytes i
    (from_byte x, from_byte y, from_byte (x ^^^ y))

  index := fun (x, y, _) => x.val * 256 + y.val

  soundness := fun (x, y, z) =>
    x.val < 256 ∧ y.val < 256 ∧ z.val = x.val ^^^ y.val
  completeness := fun (x, y, z) =>
    x.val < 256 ∧ y.val < 256 ∧ z.val = x.val ^^^ y.val

  imply_soundness := by
    intro (x, y, z)
    dsimp only
    rintro ⟨ i, h: (x, y, z) = _ ⟩
    simp only [id_eq, Prod.mk.injEq] at h

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

  implied_by_completeness := by
    intro (x, y, z) ⟨ hx, hy, h ⟩
    use concat_two_bytes ⟨ x.val, hx ⟩ ⟨ y.val, hy ⟩
    simp only [Vector.eq_mk, Array.mk.injEq, List.cons.injEq, and_true]
    rw [concat_split]
    simp [from_byte_eq, true_and, from_byte, FieldUtils.nat_to_field_of_val_eq_iff]
    apply FieldUtils.ext
    simp only [h, HXor.hXor, Xor.xor, Fin.xor, from_byte, FieldUtils.val_of_nat_to_field_eq]
}

def ByteXorTable.equiv (x y z: F p) :
  ByteXorTable.contains (x, y, z) ↔ x.val < 256 ∧ y.val < 256 ∧ z.val = x.val ^^^ y.val :=
  ⟨ByteXorTable.imply_soundness (x, y, z), ByteXorTable.implied_by_completeness (x, y, z)⟩

end Gadgets.Xor
