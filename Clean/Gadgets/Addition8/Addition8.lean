import Clean.Gadgets.Addition8.Addition8Full

namespace Gadgets.Addition8
variable {p : ℕ} [Fact p.Prime] [Fact (p > 512)]

structure Inputs (F : Type) where
  x: F
  y: F

instance : ProvableStruct Inputs where
  components := [field, field]
  to_components := fun { x, y } => .cons x (.cons y .nil)
  from_components := fun (.cons x (.cons y .nil)) => { x, y }

def main (input : Var Inputs (F p)) := do
  let ⟨x, y⟩ := input
  subcircuit Addition8Full.circuit { x, y, carry_in := 0 }

/--
  Compute the 8-bit addition of two numbers.
  Returns the sum.
-/
def circuit : FormalCircuit (F p) Inputs field where
  main
  local_length _ := 2
  output _ i0 := var ⟨i0⟩

  assumptions (input : Inputs (F p)) :=
    let ⟨x, y⟩ := input
    x.val < 256 ∧ y.val < 256

  spec (input : Inputs (F p)) (z: F p) :=
    let ⟨x, y⟩ := input
    z.val = (x.val + y.val) % 256

  -- the proofs are trivial since we are just wrapping `Addition8Full`
  soundness := by simp_all [Soundness, circuit_norm, subcircuit_norm, main,
    Addition8Full.circuit, Addition8Full.assumptions, Addition8Full.spec]

  completeness := by simp_all [Completeness, circuit_norm, subcircuit_norm, main,
    Addition8Full.circuit, Addition8Full.assumptions, Addition8Full.spec]

end Gadgets.Addition8
