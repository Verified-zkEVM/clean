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

instance elaborated : ElaboratedCircuit (F p) Inputs (Var U64 (F p)) where
  main
  local_length _ := 8
  output _ i := var_from_offset U64 i

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

theorem soundness : Soundness (F p) assumptions spec := by
  intro i env ⟨ x_var, y_var ⟩ ⟨ x, y ⟩ h_input h_assumptions h_holds
  let ⟨ x0_var, x1_var, x2_var, x3_var, x4_var, x5_var, x6_var, x7_var ⟩ := x_var
  let ⟨ y0_var, y1_var, y2_var, y3_var, y4_var, y5_var, y6_var, y7_var ⟩ := y_var
  let ⟨ x0, x1, x2, x3, x4, x5, x6, x7 ⟩ := x
  let ⟨ y0, y1, y2, y3, y4, y5, y6, y7 ⟩ := y
  obtain ⟨ x_norm, y_norm ⟩ := h_assumptions
  apply soundness_to_u64 x_norm y_norm
  simp only
  simp_all only [circuit_norm, subcircuit_norm, main, assumptions, spec, And8.circuit, eval, var_from_offset]
  simp only [Inputs.mk.injEq, U64.mk.injEq] at h_input
  obtain ⟨ hx, hy ⟩ := h_input
  obtain ⟨ h_x0, h_x1, h_x2, h_x3, h_x4, h_x5, h_x6, h_x7 ⟩ := hx
  obtain ⟨ h_y0, h_y1, h_y2, h_y3, h_y4, h_y5, h_y6, h_y7 ⟩ := hy
  rw [h_x0, h_y0, h_x1, h_y1, h_x2, h_y2, h_x3, h_y3, h_x4, h_y4, h_x5, h_y5,
    h_x6, h_y6, h_x7, h_y7] at h_holds
  simp only [And8.assumptions, And8.spec] at h_holds

  simp only [U64.is_normalized] at x_norm y_norm
  have ⟨ x0_byte, x1_byte, x2_byte, x3_byte, x4_byte, x5_byte, x6_byte, x7_byte ⟩ := x_norm
  have ⟨ y0_byte, y1_byte, y2_byte, y3_byte, y4_byte, y5_byte, y6_byte, y7_byte ⟩ := y_norm
  simp only [x0_byte, y0_byte, x1_byte, y1_byte, x2_byte, y2_byte,
    x3_byte, y3_byte, x4_byte, y4_byte, x5_byte, y5_byte,
    x6_byte, y6_byte, x7_byte, y7_byte, and_true, true_implies] at h_holds
  simp [h_holds]

theorem completeness : Completeness (F p) U64 assumptions := by
  sorry

def circuit : FormalCircuit (F p) Inputs U64 where
  assumptions
  spec
  soundness
  completeness

end Gadgets.And.And64
