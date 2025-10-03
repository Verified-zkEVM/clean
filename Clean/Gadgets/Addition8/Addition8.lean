import Clean.Gadgets.Addition8.Addition8FullCarry
import Clean.Gadgets.Boolean

namespace Gadgets
variable {p : ℕ} [Fact p.Prime] [Fact (p > 512)]

/--
Compute the 8-bit addition of two numbers with a carry-in bit.
Returns the sum.
-/
def Addition8Full.circuit : FormalCircuit (F p) Addition8FullCarry.Inputs field Unit where
  main := fun inputs => do
    let { z, .. } ← Addition8FullCarry.circuit inputs
    return z

  localLength _ := 2
  output _ i0 := var ⟨i0⟩

  Assumptions _ input :=
    input.x.val < 256 ∧ input.y.val < 256 ∧ IsBool input.carryIn

  Spec _ input z :=
    z.val = (input.x.val + input.y.val + input.carryIn.val) % 256

  -- the proofs are trivial since this just wraps `Addition8FullCarry`
  soundness := by simp_all [circuit_norm,
    Addition8FullCarry.circuit, Addition8FullCarry.Assumptions, Addition8FullCarry.Spec, forall_const]

  completeness := by simp_all [circuit_norm,
    Addition8FullCarry.circuit, Addition8FullCarry.Assumptions, forall_const]

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
def circuit : FormalCircuit (F p) Inputs field Unit where
  main := fun { x, y } =>
    Addition8Full.circuit { x, y, carryIn := 0 }

  localLength _ := 2
  output _ i0 := var ⟨i0⟩

  Assumptions _ input := input.x.val < 256 ∧ input.y.val < 256

  Spec _ input z := z.val = (input.x.val + input.y.val) % 256

  -- the proofs are trivial since this just wraps `Addition8Full`
  soundness := by
    simp_all [circuit_norm, Addition8Full.circuit, IsBool, forall_const]
  completeness := by
    simp_all [circuit_norm, Addition8Full.circuit, IsBool, forall_const]

end Addition8
end Gadgets
