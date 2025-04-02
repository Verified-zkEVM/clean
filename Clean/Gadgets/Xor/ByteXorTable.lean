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
    (x y z: F p) :
    ByteXorTable.contains (#v[x, y, z]) → z.val = Nat.xor x.val y.val := by
  sorry

def ByteXorTable.completeness
    (x y z: F p) :
    z.val = Nat.xor x.val y.val → ByteXorTable.contains (#v[x, y, z]) := by
  sorry

def ByteXorTable.equiv (x y z: F p) :
    ByteXorTable.contains (#v[x, y, z]) ↔ z.val = Nat.xor x.val y.val :=
  ⟨ByteXorTable.soundness x y z, ByteXorTable.completeness x y z⟩

def ByteXorLookup (x y z: Expression (F p)) : Lookup (F p) := {
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
