import Clean.Gadgets.ByteLookup

section
variable {p : ℕ} [Fact (p ≠ 0)] [Fact p.Prime]
variable [p_large_enough: Fact (p > 512)]

inductive Byte (F: Type) where
  | private mk : (Variable F) → Byte F

namespace Byte
def var (b: Byte (F p)) := Expression.var b.1

def witness (compute : Environment (F p) → F p) := do
  let x ← witness_var compute
  lookup (ByteLookup x)
  return Byte.mk x

instance : Coe (Byte (F p)) (Expression (F p)) where
  coe x := x.var
end Byte

end
