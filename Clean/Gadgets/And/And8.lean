import Clean.Circuit.Basic
import Clean.Types.U64
import Clean.Gadgets.Xor.ByteXorTable

variable {p : ℕ} [Fact p.Prime]
variable [p_large_enough: Fact (p > 512)]

namespace Gadgets.And

structure Inputs (F : Type) where
  x: F
  y: F

instance : ProvableType Inputs where
  size := 2
  to_elements x := #v[x.x, x.y]
  from_elements v :=
    let ⟨ .mk [x, y], _ ⟩ := v
    ⟨ x, y ⟩

structure Outputs (F : Type) where
  z: F

instance : ProvableType Outputs where
  size := 1
  to_elements x := #v[x.z]
  from_elements v :=
    let ⟨ .mk [z], _ ⟩ := v
    ⟨ z ⟩

def assumptions (input : Inputs (F p)) :=
  let ⟨x, y⟩ := input
  x.val < 256 ∧ y.val < 256

def spec (input : Inputs (F p)) (output : Outputs (F p)) :=
  let ⟨x, y⟩ := input
  let z := output.z
  z.val = Nat.land x.val y.val

def xor (x y : Expression (F p)) :  Circuit (F p) (Expression (F p)) := do
  let z ← witness (fun eval => Nat.xor (eval x).val (eval y).val)
  lookup (Gadgets.Xor.ByteXorLookup x y z)
  return z

def and8 (input : Var Inputs (F p)) : Circuit (F p) (Var Outputs (F p)) := do
  let ⟨x, y⟩ := input

  -- witness the result
  let z ← witness (fun eval => Nat.land  (eval x).val (eval y).val)

  return { z }

end Gadgets.And
