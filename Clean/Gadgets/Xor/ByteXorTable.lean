import Clean.Circuit.Basic
import Clean.Utils.Field
import Clean.Gadgets.Rotation64.Theorems

namespace Gadgets.Xor
variable {p : ℕ} [Fact (p ≠ 0)] [Fact p.Prime]
variable [p_large_enough: Fact (p > 512)]


def from_byte (x: Fin 256) : F p :=
  FieldUtils.nat_to_field x.val (by linarith [x.is_lt, p_large_enough.elim])

def ByteXorTable: Table (F p) where
  name := "ByteXor"
  length := 256*256
  arity := 3
  row i :=
    let x := i / 256
    let y := i % 256
    #v[from_byte x, from_byte y, from_byte (Nat.xor x y)]

def ByteXorTable.soundness
    (x y z: F p)
    (hx : x.val < 256)
    (hy : y.val < 256) :
    ByteXorTable.contains (#v[x, y, z]) → z.val = Nat.xor x.val y.val := by
  dsimp [Table.contains]
  rintro ⟨ i, h: #v[x, y, z] = ByteXorTable.row i ⟩
  simp [ByteXorTable] at h


def ByteXorTable.completeness
    (x y z: F p)
    (hx : x.val < 256)
    (hy : y.val < 256) :
    z.val = Nat.xor x.val y.val → ByteXorTable.contains (#v[x, y, z]) := by
  intro h
  dsimp only [ByteXorTable, Table.contains]
  use x.val * 256 + y.val
  simp [from_byte, Vector.eq_mk, Array.mk.injEq, List.cons.injEq, and_true, Fin.val_cast_of_lt hx]

  have h_x' : x.val % 256 = x.val := by
    apply (Nat.mod_eq_iff_lt (by linarith)).mpr
    exact hx

  -- have h_xy : (Fin.val ((ZMod.cast x : Fin 65536) * 256 + ZMod.cast y) / ↑256) % 256 = ZMod.cast x := by
    -- sorry

  have sanity : ((ZMod.cast x) * 256 : Fin 65536) + ZMod.cast y = 0 := by sorry

  have h_y' : y.val % 256 = y.val := by
    apply (Nat.mod_eq_iff_lt (by linarith)).mpr
    exact hy

  constructor
  rw [sanity]

def ByteXorTable.equiv (x y z: F p) (hx : x.val < 256) (hy : y.val < 256) :
    ByteXorTable.contains (#v[x, y, z]) ↔ z.val = Nat.xor x.val y.val :=
  ⟨ByteXorTable.soundness x y z hx hy, ByteXorTable.completeness x y z hx hy⟩

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
