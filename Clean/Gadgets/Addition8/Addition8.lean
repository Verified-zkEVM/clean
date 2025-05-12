import Clean.Gadgets.Addition8.Addition8Full

namespace Gadgets.Addition8
variable {p : ℕ} [Fact p.Prime]
variable [p_large_enough: Fact (p > 512)]

structure Inputs (F : Type) where
  x: F
  y: F

instance : ProvableType Inputs where
  size := 2
  to_elements s := #v[s.x, s.y]
  from_elements v :=
    let ⟨ .mk [x, y], _ ⟩ := v
    ⟨ x, y ⟩

def add8 (input : Var Inputs (F p)) := do
  let ⟨x, y⟩ := input
  let z ← subcircuit Addition8Full.circuit { x, y, carry_in := 0 }
  return z

def spec (input : Inputs (F p)) (z: F p) :=
  let ⟨x, y⟩ := input
  z.val = (x.val + y.val) % 256

def assumptions (input : Inputs (F p)) :=
  let ⟨x, y⟩ := input
  x.val < 256 ∧ y.val < 256

/--
  Compute the 8-bit addition of two numbers.
  Returns the sum.
-/
def circuit : FormalCircuit (F p) Inputs field where
  main := add8
  assumptions := assumptions
  spec := spec
  local_length _ := 2
  output _ i0 := var ⟨i0⟩

  soundness := by
    -- introductions
    rintro offset env inputs_var inputs h_inputs as
    let ⟨x, y⟩ := inputs
    let ⟨x_var, y_var⟩ := inputs_var
    intro h_holds z

    -- characterize inputs
    have hx : x_var.eval env = x := by injection h_inputs
    have hy : y_var.eval env = y := by injection h_inputs

    -- simplify constraints hypothesis
    -- it's just the `subcircuit_soundness` of `Addition8Full.circuit`
    simp [circuit_norm, subcircuit_norm, add8, Addition8Full.circuit] at h_holds

    -- rewrite input and ouput values
    rw [hx, hy, ←(by rfl : z = env.get offset)] at h_holds

    -- satisfy `Addition8Full.assumptions` by using our own assumptions
    let ⟨ asx, asy ⟩ := as
    have as': Addition8Full.assumptions { x, y, carry_in := 0 } := ⟨asx, asy, by tauto⟩
    specialize h_holds as'

    guard_hyp h_holds : Addition8Full.spec { x, y, carry_in := 0 } z

    -- unfold `Addition8Full` statements to show what the hypothesis is in our context
    dsimp [Addition8Full.spec] at h_holds
    guard_hyp h_holds : z.val = (x.val + y.val + (0 : F p).val) % 256

    simp at h_holds
    exact h_holds

  completeness := by
    -- introductions
    rintro offset env inputs_var henv inputs h_inputs
    let ⟨x, y⟩ := inputs
    let ⟨x_var, y_var⟩ := inputs_var
    rintro as

    -- characterize inputs
    have hx : x_var.eval env = x := by injection h_inputs
    have hy : y_var.eval env = y := by injection h_inputs

    -- simplify assumptions and goal
    dsimp [assumptions] at as
    simp [circuit_norm, subcircuit_norm, add8]
    rw [hx, hy]

    -- the goal is just the `subcircuit_completeness` of `Addition8Full.circuit`, i.e. the assumptions must hold
    -- simplify `Addition8Full.assumptions` and prove them easily by using our own assumptions
    dsimp [Addition8Full.circuit, Addition8Full.assumptions]
    show x.val < 256 ∧ y.val < 256 ∧ (0 = 0 ∨ 0 = 1)
    have ⟨ asx, asy ⟩ := as
    exact ⟨ asx, asy, by tauto ⟩

end Gadgets.Addition8
