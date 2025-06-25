import Clean.Circuit.Basic
import Clean.Utils.Field

namespace Gadgets.Xor
open ByteUtils
variable {p : ℕ} [Fact p.Prime] [Fact (p > 512)]

def ByteXorTable : Table (F p) fieldTriple := .fromStatic {
  name := "ByteXor"
  length := 256*256

  row i :=
    let (x, y) := split_two_bytes i
    (fromByte x, fromByte y, fromByte (x ^^^ y))

  index := fun (x, y, _) => x.val * 256 + y.val

  Spec := fun (x, y, z) =>
    x.val < 256 ∧ y.val < 256 ∧ z.val = x.val ^^^ y.val

  contains_iff := by
    intro (x, y, z)
    dsimp only
    constructor
    · rintro ⟨ i, h: (x, y, z) = _ ⟩
      simp only [id_eq, Prod.mk.injEq] at h
      rcases h with ⟨ hx, hy, hz ⟩
      and_intros
      · rw [hx]
        apply fromByte_lt
      · rw [hy]
        apply fromByte_lt
      rw [hx, hy, hz]
      repeat rw [fromByte, FieldUtils.val_of_nat_to_field_eq]
      simp only [HXor.hXor, Xor.xor, Fin.xor]
      rw [Nat.mod_eq_iff_lt (by norm_num)]
      apply Nat.xor_lt_two_pow (n:=8)
      exact (split_two_bytes i).1.is_lt
      exact (split_two_bytes i).2.is_lt
    intro ⟨ hx, hy, h ⟩
    · use concat_two_bytes ⟨ x.val, hx ⟩ ⟨ y.val, hy ⟩
      rw [concat_split]
      simp only [fromByte, FieldUtils.nat_to_field_of_val_eq_iff, Fin.xor_val_of_uInt8Size,
        Prod.mk.injEq, true_and]
      apply FieldUtils.ext
      simp [h, FieldUtils.val_of_nat_to_field_eq]
}
end Gadgets.Xor
