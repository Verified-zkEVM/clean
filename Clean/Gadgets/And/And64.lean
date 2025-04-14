import Clean.Utils.Primes
import Clean.Circuit.SubCircuit
import Clean.Types.U64
import Clean.Gadgets.And.And8

variable {p : ℕ} [Fact p.Prime]
variable [p_large_enough: Fact (p > 512)]

namespace Gadgets.And.And64
structure Inputs (F : Type) where
  x: U64 F
  y: U64 F

instance : ProvableStruct Inputs where
  components := [U64, U64]
  to_components := fun { x, y } => .cons x (.cons y .nil)
  from_components := fun (.cons x (.cons y .nil)) => { x, y }

def main (input : Var Inputs (F p)) : Circuit (F p) (Var U64 (F p))  := do
  let ⟨x, y⟩ := input
  let z0 ← subcircuit And8.circuit ⟨ x.x0, y.x0 ⟩
  let z1 ← subcircuit And8.circuit ⟨ x.x1, y.x1 ⟩
  let z2 ← subcircuit And8.circuit ⟨ x.x2, y.x2 ⟩
  let z3 ← subcircuit And8.circuit ⟨ x.x3, y.x3 ⟩
  let z4 ← subcircuit And8.circuit ⟨ x.x4, y.x4 ⟩
  let z5 ← subcircuit And8.circuit ⟨ x.x5, y.x5 ⟩
  let z6 ← subcircuit And8.circuit ⟨ x.x6, y.x6 ⟩
  let z7 ← subcircuit And8.circuit ⟨ x.x7, y.x7 ⟩
  return U64.mk z0 z1 z2 z3 z4 z5 z6 z7

def assumptions (input: Inputs (F p)) :=
  let ⟨x, y⟩ := input
  x.is_normalized ∧ y.is_normalized

def spec (input: Inputs (F p)) (z : U64 (F p)) :=
  let ⟨x, y⟩ := input
  z.value = x.value &&& y.value ∧ z.is_normalized

theorem soundness_to_u64 {x y z : U64 (F p)}
  (x_norm : x.is_normalized) (y_norm : y.is_normalized)
  (h_eq :
    x.x0.val &&& y.x0.val = z.x0.val ∧
    x.x1.val &&& y.x1.val = z.x1.val ∧
    x.x2.val &&& y.x2.val = z.x2.val ∧
    x.x3.val &&& y.x3.val = z.x3.val ∧
    x.x4.val &&& y.x4.val = z.x4.val ∧
    x.x5.val &&& y.x5.val = z.x5.val ∧
    x.x6.val &&& y.x6.val = z.x6.val ∧
    x.x7.val &&& y.x7.val = z.x7.val) :
  spec { x, y } z := by
  sorry

#eval (do main (p:=p_babybear) (default)).output 100

def circuit : FormalCircuit (F p) Inputs U64 where
  main
  assumptions
  spec

  local_length _ := 8

  -- this would be nicer if we could add/subtract/scalar-multiply entire provable types
  output := fun ⟨ x, y ⟩ i => {
    x0 := (x.x0 + y.x0 - var ⟨ i + 0 ⟩) / 2,
    x1 := (x.x1 + y.x1 - var ⟨ i + 1 ⟩) / 2,
    x2 := (x.x2 + y.x2 - var ⟨ i + 2 ⟩) / 2,
    x3 := (x.x3 + y.x3 - var ⟨ i + 3 ⟩) / 2,
    x4 := (x.x4 + y.x4 - var ⟨ i + 4 ⟩) / 2,
    x5 := (x.x5 + y.x5 - var ⟨ i + 5 ⟩) / 2,
    x6 := (x.x6 + y.x6 - var ⟨ i + 6 ⟩) / 2,
    x7 := (x.x7 + y.x7 - var ⟨ i + 7 ⟩) / 2
  }

  soundness := by
    intro i env ⟨ x_var, y_var ⟩ ⟨ x, y ⟩ h_input _ h_holds
    simp_all only [circuit_norm, main, assumptions, spec, And8.circuit]
    sorry

  completeness := by
    sorry

end Gadgets.And.And64
