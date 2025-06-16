import Clean.Gadgets.Addition8.Addition8FullCarry

namespace Gadgets.Addition8Full
variable {p : ℕ} [Fact p.Prime]
variable [p_large_enough: Fact (p > 512)]
open Addition8FullCarry (Inputs)

def main (input : Var Inputs (F p)) := do
  let ⟨x, y, carry_in⟩ := input

  let { z, .. } ← subcircuit Addition8FullCarry.circuit { x, y, carry_in }
  return z

/--
  Compute the 8-bit addition of two numbers with a carry-in bit.
  Returns the sum.
-/
def circuit : FormalCircuit (F p) Inputs field where
  main
  local_length _ := 2
  output _ i0 := var ⟨i0⟩

  assumptions (input : Inputs (F p)) :=
    let ⟨x, y, carry_in⟩ := input
    x.val < 256 ∧ y.val < 256 ∧ (carry_in = 0 ∨ carry_in = 1)

  spec (input : Inputs (F p)) (z: F p) :=
    let ⟨x, y, carry_in⟩ := input
    z.val = (x.val + y.val + carry_in.val) % 256

  -- the proofs are trivial since we are just wrapping `Addition8FullCarry`
  soundness := by simp_all [Soundness, circuit_norm, subcircuit_norm, main,
    Addition8FullCarry.circuit, Addition8FullCarry.assumptions, Addition8FullCarry.spec]

  completeness := by simp_all [Completeness, circuit_norm, subcircuit_norm, main,
    Addition8FullCarry.circuit, Addition8FullCarry.assumptions]

end Gadgets.Addition8Full
