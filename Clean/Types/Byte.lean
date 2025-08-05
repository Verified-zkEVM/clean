import Clean.Gadgets.ByteLookup

namespace Gadgets
inductive Byte (F : Type) where
  | private mk : (Variable F) → Byte F

namespace Byte
variable {p : ℕ} [Fact (p ≠ 0)] [Fact p.Prime] [Fact (p > 512)]

def var (b : Byte (F p)) := Expression.var b.1

def witness (compute : Environment (F p) → F p) := do
  let x ← witnessVar compute
  lookup ByteTable (.var x)
  return Byte.mk x

instance : Coe (Byte (F p)) (Expression (F p)) where
  coe x := x.var
end Gadgets.Byte
