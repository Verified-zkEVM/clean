import Clean.Gadgets.Addition8.Addition8FullCarry
import Clean.Gadgets.Boolean

open Clean

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

  Assumptions := fun { x, y, carryIn } =>
    x.val < 256 ∧ y.val < 256 ∧ IsBool carryIn

  Spec := fun { x, y, carryIn } z =>
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
deriving ProvableStruct

/--
Compute the 8-bit addition of two numbers.
Returns the sum.
-/
def circuit : FormalCircuit (F p) Inputs field where
  main := fun { x, y } =>
    Addition8Full.circuit { x, y, carryIn := 0 }

  elaborated := by
    haveI (input : Var Inputs (F p)) : ExplicitCircuit
        (match input with | { x, y } => subcircuit Addition8Full.circuit { x, y, carryIn := 0 }) := by
      rcases input with ⟨x, y⟩
      infer_instance
    elaborate_circuit

  Assumptions | { x, y } => x.val < 256 ∧ y.val < 256

  Spec | { x, y }, z => z.val = (x.val + y.val) % 256

  -- the proofs are trivial since this just wraps `Addition8Full`
  soundness := by
    rintro offset env ⟨vx, vy⟩ ⟨x, y⟩ hinput has hholds
    simp_all [circuit_norm, Addition8Full.circuit, IsBool]
  completeness := by
    rintro offset env ⟨vx, vy⟩ henv ⟨x, y⟩ hinput has
    simp_all [circuit_norm, Addition8Full.circuit, IsBool]

end Addition8
end Gadgets
