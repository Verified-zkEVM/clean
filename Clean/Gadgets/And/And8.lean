import Clean.Circuit.Basic
import Clean.Types.U64
import Clean.Gadgets.Xor.ByteXorTable
import Clean.Utils.Primes

variable {p : ℕ} [Fact p.Prime]
variable [p_large_enough: Fact (p > 512)]

namespace Gadgets.And

structure Inputs (F : Type) where
  x: F
  y: F

instance : ProvableStruct Inputs where
  components := [field, field]
  to_components := fun { x, y } => .cons x (.cons y .nil)
  from_components := fun (.cons x (.cons y .nil)) => { x, y }

def assumptions (input : Inputs (F p)) :=
  let ⟨x, y⟩ := input
  x.val < 256 ∧ y.val < 256

def spec (input : Inputs (F p)) (z : F p) :=
  let ⟨x, y⟩ := input
  z.val = Nat.land x.val y.val

def xor (x y : Expression (F p)) : Circuit (F p) (Expression (F p)) := do
  let z ← witness (fun eval => Nat.xor (eval x).val (eval y).val)
  lookup (Gadgets.Xor.ByteXorLookup x y z)
  return z

def main (input : Var Inputs (F p)) : Circuit (F p) (Expression (F p)) := do
  let ⟨x, y⟩ := input
  let w ← xor x y
  return (x + y - w) / 2

def circuit : FormalCircuit (F p) Inputs field where
  main
  local_length _ := 1
  output := fun ⟨ x, y ⟩ i => (x + y - var ⟨i⟩) / 2

  assumptions
  spec

  soundness := by sorry
  completeness := by sorry

end Gadgets.And
