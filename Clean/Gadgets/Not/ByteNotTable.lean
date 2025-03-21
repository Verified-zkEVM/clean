import Clean.Circuit.Basic
import Clean.Utils.Field
import Clean.Gadgets.Rotation64.Theorems

namespace Gadgets.Not
variable {p : ℕ} [Fact (p ≠ 0)] [Fact p.Prime]
variable [p_large_enough: Fact (p > 512)]


def from_byte (x: Fin 256) : F p :=
  FieldUtils.nat_to_field x.val (by linarith [x.is_lt, p_large_enough.elim])

def ByteNotTable: Table (F p) where
  name := "ByteNot"
  length := 256
  arity := 2
  row i := vec [from_byte i, from_byte (255 - i)]

def ByteNotTable.soundness
    (x y : F p)
    (hx : x.val < 256) :
    ByteNotTable.contains (vec [x, y]) → y.val = 255 - x.val := by
  sorry

def ByteNotTable.completeness
    (x y: F p)
    (hx : x.val < 256) :
    y.val = 255 - x.val → ByteNotTable.contains (vec [x, y]) := by
  sorry

def ByteNotTable.equiv (x y: F p) (hx : x.val < 256) :
    ByteNotTable.contains (vec [x, y]) ↔ y.val = 255 - x.val :=
  ⟨ByteNotTable.soundness x y hx, ByteNotTable.completeness x y hx⟩

def byte_not_lookup (x y: Expression (F p)) := lookup {
  table := ByteNotTable
  entry := vec [x, y]
  index := fun env =>
    let x := x.eval env |>.val
    if h : (x < 256)
    then ⟨x, h⟩
    else ⟨0, by show 0 < 256; norm_num⟩
}

end Gadgets.Not
