import Clean.Circuit.Basic
import Clean.Utils.Field
import Clean.Gadgets.Rotation64.Theorems

namespace Gadgets.And
variable {p : ℕ} [Fact (p ≠ 0)] [Fact p.Prime]
variable [p_large_enough: Fact (p > 512)]

def from_byte (x: Fin 256) : F p :=
  FieldUtils.nat_to_field x.val (by linarith [x.is_lt, p_large_enough.elim])

def ByteAndTable: Table (F p) where
  name := "ByteAnd"
  length := 256*256
  arity := 3
  row i :=
    let x := i / 256
    let y := i % 256
    vec [from_byte x, from_byte y, from_byte (Nat.land x y)]

def ByteAndTable.soundness
    (x y z: F p)
    (hx : x.val < 256)
    (hy : y.val < 256) :
    ByteAndTable.contains (vec [x, y, z]) → z.val = Nat.land x.val y.val := by
  sorry

def ByteAndTable.completeness
    (x y z: F p)
    (hx : x.val < 256)
    (hy : y.val < 256) :
    z.val = Nat.land x.val y.val → ByteAndTable.contains (vec [x, y, z]) := by
  sorry

def ByteAndTable.equiv (x y z: F p) (hx : x.val < 256) (hy : y.val < 256) :
    ByteAndTable.contains (vec [x, y, z]) ↔ z.val = Nat.land x.val y.val :=
  ⟨ByteAndTable.soundness x y z hx hy, ByteAndTable.completeness x y z hx hy⟩

def byte_and_lookup (x y z: Expression (F p)) := lookup {
  table := ByteAndTable
  entry := vec [x, y, z]
  index := fun env =>
    by
      let x := x.eval env |>.val
      let y := y.eval env |>.val
      dsimp [ByteAndTable]
      exact x * 256 + y
}

end Gadgets.And
