import Clean.Gadgets.Addition8.Addition8FullCarry

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

  Assumptions := fun { x, y, carry_in } =>
    x.val < 256 ∧ y.val < 256 ∧ (carry_in = 0 ∨ carry_in = 1)

  Spec := fun { x, y, carry_in } z =>
    z.val = (x.val + y.val + carry_in.val) % 256

  -- the proofs are trivial since this just wraps `Addition8FullCarry`
  soundness := by simp_all [circuit_norm, subcircuit_norm,
    Addition8FullCarry.circuit, Addition8FullCarry.Assumptions, Addition8FullCarry.Spec]

  completeness := by simp_all [circuit_norm, subcircuit_norm,
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
    Addition8Full.circuit { x, y, carry_in := 0 }

  localLength _ := 2
  output _ i0 := var ⟨i0⟩

  Assumptions | { x, y } => x.val < 256 ∧ y.val < 256

  Spec | { x, y }, z => z.val = (x.val + y.val) % 256

  -- the proofs are trivial since this just wraps `Addition8Full`
  soundness := by simp_all [circuit_norm, subcircuit_norm, Addition8Full.circuit]
  completeness := by simp_all [circuit_norm, subcircuit_norm, Addition8Full.circuit]

end Addition8
end Gadgets
