import Clean.Gadgets.Addition8.Addition8FullCarry

namespace Gadgets.Addition8Full
variable {p : ℕ} [Fact p.Prime]
variable [p_large_enough: Fact (p > 512)]

open Provable (field field2 fields)

structure InputStruct (F : Type) where
  x: F
  y: F
  carry_in: F

def Inputs (p : ℕ) : TypePair := ⟨
  InputStruct (Expression (F p)),
  InputStruct (F p)
⟩

instance : ProvableType (F p) (Inputs p) where
  size := 3
  to_vars s := vec [s.x, s.y, s.carry_in]
  from_vars v :=
    let ⟨ [x, y, carry_in], _ ⟩ := v
    ⟨ x, y, carry_in ⟩
  to_values s := vec [s.x, s.y, s.carry_in]
  from_values v :=
    let ⟨ [x, y, carry_in], _ ⟩ := v
    ⟨ x, y, carry_in ⟩

def add8_full (input : (Inputs p).var) := do
  let ⟨x, y, carry_in⟩ := input

  let res ← subcircuit Gadgets.Addition8FullCarry.circuit { x, y, carry_in }

  return res.z

def assumptions (input : (Inputs p).value) :=
  let ⟨x, y, carry_in⟩ := input
  x.val < 256 ∧ y.val < 256 ∧ (carry_in = 0 ∨ carry_in = 1)

def spec (input : (Inputs p).value) (z: F p) :=
  let ⟨x, y, carry_in⟩ := input
  z.val = (x.val + y.val + carry_in.val) % 256

/--
  Compute the 8-bit addition of two numbers with a carry-in bit.
  Returns the sum.
-/
def circuit : FormalCircuit (F p) (Inputs p) (field (F p)) where
  main := add8_full
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
    dsimp [circuit_norm, from_values, to_vars] at h_holds

    -- rewrite input and ouput values
    rw [hx, hy, hcarry_in] at h_holds
    rw [←(by rfl : z = env.get offset)] at h_holds

    -- satisfy `Add8FullCarry.assumptions` by using our own assumptions
    let ⟨ asx, asy, as_carry_in ⟩ := as
    have as': Gadgets.Addition8FullCarry.circuit.assumptions { x, y, carry_in } := ⟨asx, asy, as_carry_in⟩
    specialize h_holds (by assumption)

    guard_hyp h_holds : Gadgets.Addition8FullCarry.circuit.spec
      { x, y, carry_in }
      { z, carry_out := env.get (offset + 1) }

    -- unfold `Add8FullCarry` statements to show what the hypothesis is in our context
    dsimp [Gadgets.Addition8FullCarry.circuit, Gadgets.Addition8FullCarry.spec] at h_holds
    -- discard second part of the spec
    have ⟨ h_holds, _ ⟩ := h_holds
    guard_hyp h_holds : z.val = (x.val + y.val + carry_in.val) % 256
    exact h_holds

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
    dsimp [circuit_norm]
    rw [hx, hy, hcarry_in]

    -- the goal is just the `subcircuit_completeness` of `Add8FullCarry.circuit`, i.e. the assumptions must hold
    -- simplify `Add8Full.assumptions` and prove them easily by using our own assumptions
    dsimp [Gadgets.Addition8FullCarry.circuit, Gadgets.Addition8FullCarry.assumptions]
    have ⟨ asx, asy, as_cin ⟩ := as
    simp [asx, asy, as_cin]
  initial_offset_eq var n := by rfl

end Gadgets.Addition8Full
