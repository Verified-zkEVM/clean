import Clean.Gadgets.Addition8.Addition8FullCarry

namespace Gadgets.Addition8Full
variable {p : ℕ} [Fact p.Prime]
variable [p_large_enough: Fact (p > 512)]

structure Inputs (F : Type) where
  x: F
  y: F
  carry_in: F

instance : ProvableStruct Inputs where
  components := [field, field, field]
  to_components := fun { x, y, carry_in } => .cons x (.cons y (.cons carry_in .nil))
  from_components := fun (.cons x (.cons y (.cons carry_in .nil))) => { x, y, carry_in }

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
  output _ i0 := var ⟨i0⟩

  soundness := by
    -- introductions
    rintro offset env ⟨x_var, y_var, carry_in_var⟩ ⟨x, y, carry_in⟩ h_inputs as h_holds z

    -- simplify constraints hypothesis
    -- it's just the `subcircuit_soundness` of `Add8FullCarry.circuit`
    simp only [add8_full, circuit_norm, subcircuit_norm, Addition8FullCarry.circuit, eval] at h_holds

    -- rewrite input and ouput values
    simp only [circuit_norm, Inputs.mk.injEq] at h_inputs
    simp only [h_inputs] at h_holds
    rw [←(by rfl : z = env.get offset)] at h_holds

    -- satisfy `Add8FullCarry.assumptions` by using our own assumptions
    let ⟨ asx, asy, as_carry_in ⟩ := as
    have as': Addition8FullCarry.assumptions { x, y, carry_in } := ⟨asx, asy, as_carry_in⟩
    specialize h_holds as'

    guard_hyp h_holds : Addition8FullCarry.spec { x, y, carry_in } { z, .. }

    -- unfold `Add8FullCarry` spec to show what the hypothesis is in our context
    dsimp only [Addition8FullCarry.spec] at h_holds
    dsimp only [spec]
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
