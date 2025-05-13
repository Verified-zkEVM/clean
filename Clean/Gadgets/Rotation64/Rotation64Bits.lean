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

  set x0_l := env.get (i0)
  set x1_l := env.get (1 + i0)
  set x2_l := env.get (2 + i0)
  set x3_l := env.get (3 + i0)
  set x4_l := env.get (4 + i0)
  set x5_l := env.get (5 + i0)
  set x6_l := env.get (6 + i0)
  set x7_l := env.get (7 + i0)
  set x0_h := env.get (8 + i0)
  set x1_h := env.get (9 + i0)
  set x2_h := env.get (10 + i0)
  set x3_h := env.get (11 + i0)
  set x4_h := env.get (12 + i0)
  set x5_h := env.get (13 + i0)
  set x6_h := env.get (14 + i0)
  set x7_h := env.get (15 + i0)
  set y0 := env.get (16 + i0)
  set y1 := env.get (17 + i0)
  set y2 := env.get (18 + i0)
  set y3 := env.get (19 + i0)
  set y4 := env.get (20 + i0)
  set y5 := env.get (21 + i0)
  set y6 := env.get (22 + i0)
  set y7 := env.get (23 + i0)

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
  save
  simp [and_assoc] at h_holds
  obtain ⟨h_decomposition, y_normalized, eq1, eq2, eq3, eq4, eq5, eq6, eq7⟩ := h_holds
  specialize h_decomposition x_normalized
  obtain ⟨h_x0, h_x1, h_x2, h_x3, h_x4, h_x5, h_x6, h_x7⟩ := h_decomposition


  -- now the statement is reasonable

  sorry

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
