import Clean.Gadgets.Addition8.Addition8FullCarry

namespace Gadgets.Addition8Full
variable {p : ℕ} [Fact p.Prime]
variable [p_large_enough: Fact (p > 512)]

structure Inputs (F : Type) where
  x: F
  y: F
  carry_in: F

instance : ProvableType Inputs where
  size := 3
  to_elements s := #v[s.x, s.y, s.carry_in]
  from_elements v :=
    let ⟨ .mk [x, y, carry_in], _ ⟩ := v
    ⟨ x, y, carry_in ⟩

def add8_full (input : Var Inputs (F p)) := do
  let ⟨x, y, carry_in⟩ := input

  let res ← subcircuit Gadgets.Addition8FullCarry.circuit { x, y, carry_in }
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
def circuit : FormalCircuit (F p) Inputs Provable.field where
  circuit := {
    main := add8_full
    local_length _ := 2
    output _ i0 := var ⟨i0⟩
  }
  assumptions := assumptions
  spec := spec

  soundness := by
    -- introductions
    rintro offset env inputs_var inputs h_inputs as
    let ⟨x, y, carry_in⟩ := inputs
    let ⟨x_var, y_var, carry_in_var⟩ := inputs_var
    intro h_holds z

    -- characterize inputs
    have hx : x_var.eval env = x := by injection h_inputs
    have hy : y_var.eval env = y := by injection h_inputs
    have hcarry_in : carry_in_var.eval env = carry_in := by injection h_inputs

    -- simplify constraints hypothesis
    -- it's just the `subcircuit_soundness` of `Add8FullCarry.circuit`
    simp only [add8_full, circuit_norm, subcircuit_norm, Addition8FullCarry.circuit] at h_holds

    -- rewrite input and ouput values
    rw [hx, hy, hcarry_in, ←(by rfl : z = env.get offset)] at h_holds

    -- satisfy `Add8FullCarry.assumptions` by using our own assumptions
    let ⟨ asx, asy, as_carry_in ⟩ := as
    have as': Addition8FullCarry.assumptions { x, y, carry_in } := ⟨asx, asy, as_carry_in⟩
    specialize h_holds as'

    guard_hyp h_holds : Addition8FullCarry.spec { x, y, carry_in } { z, .. }

    -- unfold `Add8FullCarry` spec to show what the hypothesis is in our context
    dsimp [Addition8FullCarry.spec] at h_holds
    dsimp [spec]
    -- discard second part of the spec
    exact h_holds.left

  completeness := by
    -- introductions
    rintro offset env inputs_var henv inputs h_inputs
    let ⟨x, y, carry_in⟩ := inputs
    let ⟨x_var, y_var, carry_in_var⟩ := inputs_var
    rintro as

    -- characterize inputs
    have hx : x_var.eval env = x := by injection h_inputs
    have hy : y_var.eval env = y := by injection h_inputs
    have hcarry_in : carry_in_var.eval env = carry_in := by injection h_inputs

    -- simplify assumptions and goal
    dsimp [assumptions] at as
    simp only [circuit_norm, add8_full, subcircuit_norm]
    rw [hx, hy, hcarry_in]

    -- the goal is just the `subcircuit_completeness` of `Add8FullCarry.circuit`, i.e. the assumptions must hold.
    -- this is equivalent to our own assumptions
    exact as

end Gadgets.Addition8Full
