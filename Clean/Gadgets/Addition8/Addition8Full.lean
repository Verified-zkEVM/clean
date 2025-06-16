import Clean.Gadgets.Addition8.Addition8FullCarry

namespace Gadgets.Addition8Full
variable {p : ℕ} [Fact p.Prime]
variable [p_large_enough: Fact (p > 512)]
open Addition8FullCarry (Inputs)

def add8_full (input : Var Inputs (F p)) := do
  let ⟨x, y, carry_in⟩ := input

  let res ← subcircuit Addition8FullCarry.circuit { x, y, carry_in }
  return res.z

def assumptions (input : Inputs (F p)) :=
  let ⟨x, y, carry_in⟩ := input
  x.val < 256 ∧ y.val < 256 ∧ (carry_in = 0 ∨ carry_in = 1)

def spec (input : Inputs (F p)) (z: F p) :=
  let ⟨x, y, carry_in⟩ := input
  z.val = (x.val + y.val + carry_in.val) % 256

/--
  Compute the 8-bit addition of two numbers with a carry-in bit.
  Returns the sum.
-/
def circuit : FormalCircuit (F p) Inputs field where
  main := add8_full
  assumptions := assumptions
  spec := spec
  local_length _ := 2
  output input i0 := (Addition8FullCarry.circuit.out input i0).z

  soundness := by
    -- introductions
    rintro offset env ⟨x_var, y_var, carry_in_var⟩ ⟨x, y, carry_in⟩ h_inputs as h_holds

    -- simplify constraints and goal
    -- constraints are just the `subcircuit_soundness` of `Add8FullCarry.circuit`
    simp only [add8_full, spec, circuit_norm, subcircuit_norm, Addition8FullCarry.circuit, ElaboratedCircuit.out] at h_holds ⊢

    -- rewrite input and ouput values
    simp only [circuit_norm, Inputs.mk.injEq] at h_inputs
    simp only [h_inputs] at h_holds
    set z := env.get offset

    -- satisfy `Add8FullCarry.assumptions` by using our own assumptions
    have as': Addition8FullCarry.assumptions { x, y, carry_in } := as
    specialize h_holds as'

    change Addition8FullCarry.spec { x, y, carry_in } { z, .. } at h_holds

    -- unfold `Add8FullCarry` spec to show what the hypothesis is in our context
    dsimp only [Addition8FullCarry.spec] at h_holds
    -- discard second part of the spec
    exact h_holds.left

  completeness := by
    -- introductions
    rintro offset env ⟨x_var, y_var, carry_in_var⟩ henv ⟨x, y, carry_in⟩ h_inputs as

    -- simplify assumptions and goal
    simp_all only [circuit_norm, Inputs.mk.injEq, assumptions, add8_full, eval,
      subcircuit_norm, Addition8FullCarry.circuit]

    -- the goal is just the `subcircuit_completeness` of `Add8FullCarry.circuit`, i.e. the assumptions must hold.
    -- this is equivalent to our own assumptions
    simp only [Addition8FullCarry.assumptions]
    exact as

end Gadgets.Addition8Full
