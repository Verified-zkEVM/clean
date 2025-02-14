import Clean.Circuit.Basic
import Clean.GadgetsNew.ByteLookup
import Clean.Types.U64

variable {p : ℕ} [Fact (p ≠ 0)] [Fact p.Prime]
variable [p_large_enough: Fact (p > 512)]

def split_2_bytes (x : Fin 65536) : Fin 256 × Fin 256 :=
  (x / 256, x % 256)

def concat_2_bytes (x : Fin 256) (y : Fin 256) : Fin 65536 :=
  x * 256 + y

def XorTable : Table (F p) where
  name := "Xor"
  length := 65536
  arity := 3
  row i :=
    let (x, y) := split_2_bytes i
    vec [from_byte x, from_byte y, from_byte (Nat.xor x y)]

def XorTable.soundness (x y z: F p) :
  XorTable.contains (vec [x, y, z])
  → x.val < 256 ∧ y.val < 256 ∧ z.val = Nat.xor x.val y.val := by
  sorry

def XorTable.completeness (x y z: F p) :
  x.val < 256 ∧ y.val < 256 ∧ z.val = Nat.xor x.val y.val
  → XorTable.contains (vec [x, y, z]) := by
  sorry

namespace Bytes
def xor (x y : Expression (F p)) : Circuit (F p) (Expression (F p)) := do
  let z ← witness (fun () => Nat.xor x.eval.val y.eval.val)
  lookup {
    table := XorTable,
    entry := vec [x, y, z],
    index := fun () => concat_2_bytes x.eval.val y.eval.val
  }
  return z

def and (x y : Expression (F p)) : Circuit (F p) (Expression (F p)) := do
  let z ← witness (fun () => Nat.land x.eval.val y.eval.val)
  /-
  2*(x AND y) + (x XOR y) = x + y

  2*z + (x XOR y) === x + y
  -/
  let xor_x_y ← xor x y
  assert_zero ((const 2)*z + xor_x_y - x - y)
  return z

def not (x : Expression (F p)) : Circuit (F p) (Expression (F p)) := do
  let not_x := (const 255) - x
  return not_x
end Bytes
