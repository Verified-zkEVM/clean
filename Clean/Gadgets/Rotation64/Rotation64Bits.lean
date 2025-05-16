import Clean.Types.U64
import Clean.Circuit.SubCircuit
import Clean.Gadgets.Rotation64.Theorems
import Clean.Gadgets.Rotation64.Rotation64Bytes
import Clean.Gadgets.Rotation64.ByteRotationTable
import Clean.Gadgets.ByteDecomposition
import Clean.Circuit.Provable

namespace Gadgets.Rotation64Bits
variable {p : ℕ} [Fact p.Prime]
variable [p_large_enough: Fact (p > 2^16 + 2^8)]

instance : Fact (p > 512) := by
  constructor
  linarith [p_large_enough.elim]

open Gadgets.Rotation64.Theorems (rot_right64)

/--
  Rotate the 64-bit integer by `offset` bits
-/
def rot64_bits (offset : Fin 8) (x : Var U64 (F p)) : Circuit (F p) (Var U64 (F p)) := do

  let two_power : F p := 2^offset.val

  let ⟨low, high⟩ ← subcircuit (Gadgets.U64ByteDecomposition.circuit offset) x
  let ⟨x0_l, x1_l, x2_l, x3_l, x4_l, x5_l, x6_l, x7_l⟩ := low
  let ⟨x0_h, x1_h, x2_h, x3_h, x4_h, x5_h, x6_h, x7_h⟩ := high

  let ⟨y0, y1, y2, y3, y4, y5, y6, y7⟩ ← U64.witness fun _env => U64.mk 0 0 0 0 0 0 0 0

  assert_zero (x1_l * two_power + x0_h - y0)
  assert_zero (x2_l * two_power + x1_h - y1)
  assert_zero (x3_l * two_power + x2_h - y2)
  assert_zero (x4_l * two_power + x3_h - y3)
  assert_zero (x5_l * two_power + x4_h - y4)
  assert_zero (x6_l * two_power + x5_h - y5)
  assert_zero (x7_l * two_power + x6_h - y6)
  assert_zero (x0_l * two_power + x7_h - y7)
  return ⟨y0, y1, y2, y3, y4, y5, y6, y7⟩

instance lawful (off : Fin 8) : ConstantLawfulCircuits (F := (F p)) (rot64_bits off) := by infer_constant_lawful_circuits

def assumptions (input : U64 (F p)) := input.is_normalized

def spec (offset : Fin 8) (x : U64 (F p)) (y: U64 (F p)) :=
  y.value = rot_right64 x.value offset.val
  ∧ y.is_normalized

-- #eval! (rot64_bits (p:=p_babybear) 0) default |>.operations.local_length
-- #eval! (rot64_bits (p:=p_babybear) 0) default |>.output
def elaborated (off : Fin 8) : ElaboratedCircuit (F p) U64 (Var U64 (F p)) where
  main := rot64_bits off
  local_length _ := 24
  output _inputs i0 := var_from_offset U64 (i0 + 16)
  initial_offset_eq := by
    intros
    simp only [rot64_bits]
    rfl
  local_length_eq := by
    intros
    simp only [rot64_bits]
    rfl

theorem rotation64_bits_soundness (offset : Fin 8) {
      x0 x1 x2 x3 x4 x5 x6 x7
      y0 y1 y2 y3 y4 y5 y6 y7
      x0_l x1_l x2_l x3_l x4_l x5_l x6_l x7_l
      x0_h x1_h x2_h x3_h x4_h x5_h x6_h x7_h : F p
    }
    (h_x0_l : x0_l.val = x0.val % 2 ^ offset.val)
    (h_x0_h : x0_h.val = x0.val / 2 ^ offset.val)
    (h_x1_l : x1_l.val = x1.val % 2 ^ offset.val)
    (h_x1_h : x1_h.val = x1.val / 2 ^ offset.val)
    (h_x2_l : x2_l.val = x2.val % 2 ^ offset.val)
    (h_x2_h : x2_h.val = x2.val / 2 ^ offset.val)
    (h_x3_l : x3_l.val = x3.val % 2 ^ offset.val)
    (h_x3_h : x3_h.val = x3.val / 2 ^ offset.val)
    (h_x4_l : x4_l.val = x4.val % 2 ^ offset.val)
    (h_x4_h : x4_h.val = x4.val / 2 ^ offset.val)
    (h_x5_l : x5_l.val = x5.val % 2 ^ offset.val)
    (h_x5_h : x5_h.val = x5.val / 2 ^ offset.val)
    (h_x6_l : x6_l.val = x6.val % 2 ^ offset.val)
    (h_x6_h : x6_h.val = x6.val / 2 ^ offset.val)
    (h_x7_l : x7_l.val = x7.val % 2 ^ offset.val)
    (h_x7_h : x7_h.val = x7.val / 2 ^ offset.val)
    (eq0 : x1_l * 2 ^ offset.val + (x0_h - y0) = 0)
    (eq1 : x2_l * 2 ^ offset.val + (x1_h - y1) = 0)
    (eq2 : x3_l * 2 ^ offset.val + (x2_h - y2) = 0)
    (eq3 : x4_l * 2 ^ offset.val + (x3_h - y3) = 0)
    (eq4 : x5_l * 2 ^ offset.val + (x4_h - y4) = 0)
    (eq5 : x6_l * 2 ^ offset.val + (x5_h - y5) = 0)
    (eq6 : x7_l * 2 ^ offset.val + (x6_h - y6) = 0)
    (eq7 : x0_l * 2 ^ offset.val + (x7_h - y7) = 0):
    let x_val := x0.val + x1.val * 256 + x2.val * 256 ^ 2 + x3.val * 256 ^ 3 + x4.val * 256 ^ 4 +
      x5.val * 256 ^ 5 + x6.val * 256 ^ 6 + x7.val * 256 ^ 7
    let y_val := y0.val + y1.val * 256 + y2.val * 256 ^ 2 + y3.val * 256 ^ 3 + y4.val * 256 ^ 4 +
      y5.val * 256 ^ 5 + y6.val * 256 ^ 6 + y7.val * 256 ^ 7
    y_val = (x_val) % 2 ^ (offset.val % 64) * 2 ^ (64 - offset.val % 64) + (x_val) / 2 ^ (offset.val % 64) := by

  rw [←add_sub_assoc, sub_eq_add_neg] at eq0 eq1 eq2 eq3 eq4 eq5 eq6 eq7
  have h := ByteDecomposition.byte_decomposition_lift offset y0 x2_l x1_l
  sorry

set_option maxHeartbeats 10000000
theorem soundness (offset : Fin 8) : Soundness (F p) (circuit := elaborated offset) assumptions (spec offset) := by
  intro i0 env ⟨x0_var, x1_var, x2_var, x3_var, x4_var, x5_var, x6_var, x7_var ⟩ ⟨x0, x1, x2, x3, x4, x5, x6, x7⟩ h_input x_normalized h_holds

  -- TODO: this simplification is slow
  simp [circuit_norm, elaborated, rot64_bits, U64.witness] at h_holds
  simp [subcircuit_norm, U64.AssertNormalized.assumptions, U64.AssertNormalized.circuit, circuit_norm] at h_holds
  simp [U64ByteDecomposition.circuit, U64ByteDecomposition.elaborated, U64ByteDecomposition.spec,
    U64ByteDecomposition.assumptions, U64.AssertNormalized.spec, circuit_norm, eval] at h_holds

  simp only [assumptions] at x_normalized
  simp [circuit_norm, spec, rot_right64, eval, elaborated, var_from_offset]
  ring_nf at *

  rw [
    show Expression.eval env x0_var = x0 by injections h_input,
    show Expression.eval env x1_var = x1 by injections h_input,
    show Expression.eval env x2_var = x2 by injections h_input,
    show Expression.eval env x3_var = x3 by injections h_input,
    show Expression.eval env x4_var = x4 by injections h_input,
    show Expression.eval env x5_var = x5 by injections h_input,
    show Expression.eval env x6_var = x6 by injections h_input,
    show Expression.eval env x7_var = x7 by injections h_input,
  ] at h_holds
  simp [and_assoc] at h_holds
  obtain ⟨h_decomposition, y_normalized, eq0, eq1, eq2, eq3, eq4, eq5, eq6, eq7⟩ := h_holds
  specialize h_decomposition x_normalized
  obtain ⟨h_x0_l, h_x0_h, h_x1_l, h_x1_h, h_x2_l, h_x2_h, h_x3_l, h_x3_h,
    h_x4_l, h_x4_h, h_x5_l, h_x5_h, h_x6_l, h_x6_h, h_x7_l, h_x7_h⟩ := h_decomposition
  simp only [U64.value, y_normalized, and_true]
  rw [rotation64_bits_soundness offset
    h_x0_l h_x0_h h_x1_l h_x1_h h_x2_l h_x2_h h_x3_l h_x3_h
    h_x4_l h_x4_h h_x5_l h_x5_h h_x6_l h_x6_h h_x7_l h_x7_h
    eq0 eq1 eq2 eq3 eq4 eq5 eq6 eq7]


theorem completeness (offset : Fin 8) : Completeness (F p) (circuit := elaborated offset) U64 assumptions := by
  sorry

def circuit (offset : Fin 8) : FormalCircuit (F p) U64 U64 := {
  elaborated offset with
  assumptions := assumptions
  spec := spec offset
  soundness := soundness offset
  completeness := completeness offset
}

end Gadgets.Rotation64Bits
