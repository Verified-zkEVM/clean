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

  Assumptions := fun { x, y, carryIn } =>
    x.val < 256 ∧ y.val < 256 ∧ IsBool carryIn

  Spec := fun { x, y, carryIn } z =>
    z.val = (x.val + y.val + carryIn.val) % 256

  -- the proofs are trivial since this just wraps `Addition8FullCarry`
  soundness := by simp_all [circuit_norm,
    Addition8FullCarry.circuit, Addition8FullCarry.Assumptions, Addition8FullCarry.Spec]

  completeness := by simp_all [circuit_norm,
    Addition8FullCarry.circuit, Addition8FullCarry.Assumptions]

  computableWitnesses := by
    intro n input env env'
    refine ⟨?_, ?_⟩
    · simp only [circuit_norm]
      intro h_input
      exact FormalCircuit.toSubcircuit_computableWitnesses _
        (by simpa only [circuit_norm] using h_input)
    · -- output is the witnessed sum, fixed by environment agreement
      intro _ h_agrees
      simp only [circuit_norm] at h_agrees ⊢
      exact h_agrees.1 n (by omega)

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

  Assumptions | { x, y } => x.val < 256 ∧ y.val < 256

  Spec | { x, y }, z => z.val = (x.val + y.val) % 256

  -- the proofs are trivial since this just wraps `Addition8Full`
  soundness := by
    simp_all [circuit_norm, Addition8Full.circuit, IsBool]
  completeness := by
    simp_all [circuit_norm, Addition8Full.circuit, IsBool]

  computableWitnesses := by
    intro n input env env'
    refine ⟨?_, ?_⟩
    · simp only [circuit_norm]
      intro h_input
      apply FormalCircuit.toSubcircuit_computableWitnesses
      -- the child input adds `carryIn := 0`, so rebuild the 3-field agreement from `x`, `y`
      simp only [circuit_norm, Inputs.mk.injEq] at h_input
      obtain ⟨hx, hy⟩ := h_input
      simp only [circuit_norm, hx, hy]
    · -- output is the witnessed sum, fixed by environment agreement
      intro _ h_agrees
      simp only [circuit_norm] at h_agrees ⊢
      exact h_agrees.1 n (by omega)

end Addition8
end Gadgets
