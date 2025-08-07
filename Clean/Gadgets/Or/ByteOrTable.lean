import Clean.Circuit.Basic
import Clean.Utils.Field

namespace Gadgets.Or
open ByteUtils
variable {p : ℕ} [Fact p.Prime] [Fact (p > 512)]

def ByteOrTable : Table (F p) fieldTriple := .fromStatic {
  name := "ByteOr"
  length := 256*256

  row i :=
    let (x, y) := splitTwoBytes i
    (fromByte x, fromByte y, fromByte (x ||| y))

  index := fun (x, y, _) => x.val*256 + y.val

  Spec := fun (x, y, z) =>
    x.val < 256 ∧ y.val < 256 ∧ z.val = x.val ||| y.val

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
      repeat rw [fromByte, FieldUtils.val_of_natToField_eq]
      norm_num
    intro ⟨ hx, hy, h ⟩
    · use concatTwoBytes ⟨ x.val, hx ⟩ ⟨ y.val, hy ⟩
      rw [splitTwoBytes_concatTwoBytes]
      simp only [fromByte, FieldUtils.natToField_of_val_eq_iff,
        Prod.mk.injEq, true_and]
      apply FieldUtils.ext
      simp [h, FieldUtils.val_of_natToField_eq]
}
end Gadgets.Or
