import Clean.Gadgets.Addition8.Addition8FullCarry
import Clean.Gadgets.Boolean

namespace Gadgets
variable {p : ℕ} [Fact p.Prime] [Fact (p > 512)]

/--
Compute the 8-bit addition of two numbers with a carry-in bit.
Returns the sum.
-/
def Addition8Full.circuit {sentences : PropertySet (F p)} (order : SentenceOrder sentences)
    : FormalCircuit order Addition8FullCarry.Inputs field where
  main := fun inputs => do
    let { z, .. } ← Addition8FullCarry.circuit order inputs
    return z

  localLength _ := 2
  output _ i0 := var ⟨i0⟩

  Assumptions := fun { x, y, carryIn } =>
    x.val < 256 ∧ y.val < 256 ∧ IsBool carryIn

  Spec _ := fun { x, y, carryIn } z =>
    z.val = (x.val + y.val + carryIn.val) % 256

  -- the proofs are trivial since this just wraps `Addition8FullCarry`
  soundness := by simp_all [circuit_norm,
    Addition8FullCarry.circuit, Addition8FullCarry.Assumptions, Addition8FullCarry.Spec]

  completeness := by simp_all [circuit_norm,
    Addition8FullCarry.circuit, Addition8FullCarry.Assumptions]

namespace Addition8
structure Inputs (F : Type) where
  x: F
  y: F

instance : ProvableStruct Inputs where
  components := [field, field]
  toComponents := fun { x, y } => .cons x (.cons y .nil)
  fromComponents := fun (.cons x (.cons y .nil)) => { x, y }

/--
Compute the 8-bit addition of two numbers.
Returns the sum.
-/
def circuit {sentences : PropertySet (F p)} (order : SentenceOrder sentences)
    : FormalCircuit order Inputs field where
  main := fun { x, y } =>
    Addition8Full.circuit order { x, y, carryIn := 0 }

  localLength _ := 2
  output _ i0 := var ⟨i0⟩

  Assumptions | { x, y } => x.val < 256 ∧ y.val < 256

  Spec _ | { x, y }, z => z.val = (x.val + y.val) % 256

  -- the proofs are trivial since this just wraps `Addition8Full`
  soundness := by
    simp_all [circuit_norm, Addition8Full.circuit, IsBool]
  completeness := by
    simp_all [circuit_norm, Addition8Full.circuit, IsBool]

end Addition8
end Gadgets
