import Clean.Types.U32
import Clean.Circuit.SubCircuit
import Clean.Gadgets.Rotation32.Theorems
import Clean.Gadgets.Rotation32.Rotation32Bytes
import Clean.Gadgets.ByteDecomposition.ByteDecomposition
import Clean.Circuit.Provable

namespace Gadgets.Rotation32Bits
variable {p : ℕ} [Fact p.Prime]
variable [p_large_enough: Fact (p > 2^16 + 2^8)]

instance : Fact (p > 512) := by
  constructor
  linarith [p_large_enough.elim]

open Bitwise (rot_right32)
open Gadgets.Rotation32.Theorems (rotation32_bits_soundness)

/--
  Rotate the 32-bit integer by `offset` bits
-/
def rot32_bits (offset : Fin 8) (x : Var U32 (F p)) : Circuit (F p) (Var U32 (F p)) := do
  let base : F p := (2^(8 - offset.val) % 256 : ℕ)

  let ⟨low, high⟩ ← subcircuit (Gadgets.U32ByteDecomposition.circuit offset) x
  let ⟨x0_l, x1_l, x2_l, x3_l⟩ := low
  let ⟨x0_h, x1_h, x2_h, x3_h⟩ := high

  let ⟨y0, y1, y2, y3⟩ ← U32.witness fun _env => U32.mk 0 0 0 0

  y0.assert_equals (x1_l * base + x0_h)
  y1.assert_equals (x2_l * base + x1_h)
  y2.assert_equals (x3_l * base + x2_h)
  y3.assert_equals (x0_l * base + x3_h)

  return ⟨y0, y1, y2, y3⟩

def assumptions (input : U32 (F p)) := input.is_normalized

def spec (offset : Fin 8) (x : U32 (F p)) (y: U32 (F p)) :=
  y.value = rot_right32 x.value offset.val
  ∧ y.is_normalized

-- #eval! (rot32_bits (p:=p_babybear) 0) default |>.operations.local_length
-- #eval! (rot32_bits (p:=p_babybear) 0) default |>.output
def elaborated (off : Fin 8) : ElaboratedCircuit (F p) U32 U32 where
  main := rot32_bits off
  local_length _ := 12
  output _inputs i0 := var_from_offset U32 (i0 + 8)


theorem soundness (offset : Fin 8) : Soundness (F p) (elaborated offset) assumptions (spec offset) := by
  intro i0 env ⟨ x0_var, x1_var, x2_var, x3_var ⟩ ⟨ x0, x1, x2, x3 ⟩ h_input x_normalized h_holds

  dsimp only [circuit_norm, elaborated, rot32_bits, U32.witness, U32.AssertNormalized.circuit] at h_holds
  simp only [circuit_norm, elaborated, U32ByteDecomposition.circuit, U32ByteDecomposition.elaborated, U32.AssertNormalized.circuit] at h_holds
  dsimp only [circuit_norm, subcircuit_norm, U32.AssertNormalized.assumptions, U32.AssertNormalized.spec,
    U32ByteDecomposition.assumptions, U32ByteDecomposition.spec] at h_holds
  simp only [circuit_norm, eval, var_from_offset, Vector.mapRange] at h_holds

  simp only [assumptions] at x_normalized
  simp [circuit_norm, spec, rot_right32, eval, elaborated, var_from_offset, Vector.mapRange]

  rw [
    show Expression.eval env x0_var = x0 by injections h_input,
    show Expression.eval env x1_var = x1 by injections h_input,
    show Expression.eval env x2_var = x2 by injections h_input,
    show Expression.eval env x3_var = x3 by injections h_input,
  ] at h_holds
  obtain ⟨h_decomposition, y_normalized, eq0, eq1, eq2, eq3⟩ := h_holds
  specialize h_decomposition x_normalized
  obtain ⟨h_x0_l, h_x0_h, h_x1_l, h_x1_h, h_x2_l, h_x2_h, h_x3_l, h_x3_h⟩ := h_decomposition
  simp only [U32.value, y_normalized, and_true]
  obtain ⟨h_x0, h_x1, h_x2, h_x3⟩ := x_normalized
  rw [rotation32_bits_soundness offset
    h_x0 h_x1 h_x2 h_x3
    h_x0_l h_x0_h h_x1_l h_x1_h h_x2_l h_x2_h h_x3_l h_x3_h
    eq0 eq1 eq2 eq3]

theorem completeness (offset : Fin 8) : Completeness (F p) (elaborated offset) assumptions := by
  sorry

def circuit (offset : Fin 8) : FormalCircuit (F p) U32 U32 := {
  elaborated offset with
  assumptions := assumptions
  spec := spec offset
  soundness := soundness offset
  completeness := completeness offset
}

end Gadgets.Rotation32Bits
