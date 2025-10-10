import Clean.Gadgets.Addition8.Addition8FullCarry
import Clean.Gadgets.Boolean

namespace Gadgets
variable {p : ℕ} [Fact p.Prime] [Fact (p > 512)]

/--
Compute the 8-bit addition of two numbers with a carry-in bit.
Returns the sum.
-/
def Addition8Full.circuit : FormalCircuit (F p) Addition8FullCarry.Inputs field where
  main := fun inputs => do
    let { z, .. } ← Addition8FullCarry.circuit inputs
    return z

  localLength _ := 2
  output _ i0 := var ⟨i0⟩
  yields_eq := by intros; simp only [circuit_norm, Addition8FullCarry.circuit]

  Assumptions := fun { x, y, carryIn } _ =>
    x.val < 256 ∧ y.val < 256 ∧ IsBool carryIn

  Spec := fun { x, y, carryIn } z _ =>
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
def circuit : FormalCircuit (F p) Inputs field where
  main := fun { x, y } =>
    Addition8Full.circuit { x, y, carryIn := 0 }

  localLength _ := 2
  output _ i0 := var ⟨i0⟩
  yields_eq := by intros; simp only [circuit_norm, Addition8Full.circuit]

  Assumptions | { x, y }, _ => x.val < 256 ∧ y.val < 256

  Spec | { x, y }, z, _ => z.val = (x.val + y.val) % 256

  -- the proofs are trivial since this just wraps `Addition8Full`
  soundness := by
    simp_all [circuit_norm, Addition8Full.circuit, Addition8FullCarry.circuit, IsBool]
  completeness := by
    simp_all [circuit_norm, Addition8Full.circuit, Addition8FullCarry.circuit, IsBool]

end Addition8
end Gadgets
