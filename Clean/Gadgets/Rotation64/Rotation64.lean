import Clean.Types.U64
import Clean.Gadgets.Rotation64.Theorems
import Clean.Gadgets.Rotation64.Rotation64Bytes
import Clean.Gadgets.Rotation64.ByteRotationTable

namespace Gadgets.Rotation64
variable {p : ℕ} [Fact p.Prime]
variable [p_large_enough: Fact (p > 512)]

open Gadgets.Rotation64.Theorems (rot_right64 rot_right8)
open Gadgets.Rotation64 (byte_rotation_lookup)

structure Inputs (F : Type) where
  x: U64 F

instance instProvableTypeInputs : ProvableType Inputs where
  size := ProvableType.size U64
  to_elements x := (ProvableType.to_elements x.x)
  from_elements v :=
    let ⟨ [x0, x1, x2, x3, x4, x5, x6, x7], _ ⟩ := v
    ⟨ ⟨ x0, x1, x2, x3, x4, x5, x6, x7 ⟩ ⟩

structure Outputs (F : Type) where
  z: U64 F

instance instProvableTypeOutputs : ProvableType Outputs where
  size := ProvableType.size U64
  to_elements x := (ProvableType.to_elements x.z)
  from_elements v :=
    let ⟨ [z0, z1, z2, z3, z4, z5, z6, z7], _ ⟩ := v
    ⟨ ⟨ z0, z1, z2, z3, z4, z5, z6, z7 ⟩ ⟩


/--
  Rotate the 64-bit integer by `offset` bits
-/
def rot64_circuit (offset : Fin 64) (input : Var Inputs (F p)) : Circuit (F p) (Var Outputs (F p)) := do
  let byte_offset := offset / 8
  let bit_offset : ℕ := (offset % 8).val

  let x := input.x

  -- apply the byte rotation
  let ⟨out⟩ ← subcircuit (Gadgets.Rotation64Bytes.circuit byte_offset) { x }

  -- apply the bit rotation
  let ⟨x0, x1, x2, x3, x4, x5, x6, x7⟩ := out



  let x0_l ← witness (fun env => 0)
  let x0_h ← witness (fun env => 0)
  let x1_l ← witness (fun env => 0)
  let x1_h ← witness (fun env => 0)
  let x2_l ← witness (fun env => 0)
  let x2_h ← witness (fun env => 0)
  let x3_l ← witness (fun env => 0)
  let x3_h ← witness (fun env => 0)
  let x4_l ← witness (fun env => 0)
  let x4_h ← witness (fun env => 0)
  let x5_l ← witness (fun env => 0)
  let x5_h ← witness (fun env => 0)
  let x6_l ← witness (fun env => 0)
  let x6_h ← witness (fun env => 0)
  let x7_l ← witness (fun env => 0)
  let x7_h ← witness (fun env => 0)

  assert_zero (x0_l + ((2 : ℕ)^bit_offset : F p) * x0_h - x0)
  assert_zero (x1_l + ((2 : ℕ)^bit_offset : F p) * x1_h - x1)
  assert_zero (x2_l + ((2 : ℕ)^bit_offset : F p) * x2_h - x2)
  assert_zero (x3_l + ((2 : ℕ)^bit_offset : F p) * x3_h - x3)
  assert_zero (x4_l + ((2 : ℕ)^bit_offset : F p) * x4_h - x4)
  assert_zero (x5_l + ((2 : ℕ)^bit_offset : F p) * x5_h - x5)
  assert_zero (x6_l + ((2 : ℕ)^bit_offset : F p) * x6_h - x6)
  assert_zero (x7_l + ((2 : ℕ)^bit_offset : F p) * x7_h - x7)

  let ⟨y0, y1, y2, y3, y4, y5, y6, y7⟩ ← U64.witness (fun env => U64.mk 0 0 0 0 0 0 0 0)

  assert_zero (x1_l * ((2 : ℕ)^bit_offset : F p) + x0_h - y0)
  assert_zero (x2_l * ((2 : ℕ)^bit_offset : F p) + x1_h - y1)
  assert_zero (x3_l * ((2 : ℕ)^bit_offset : F p) + x2_h - y2)
  assert_zero (x4_l * ((2 : ℕ)^bit_offset : F p) + x3_h - y3)
  assert_zero (x5_l * ((2 : ℕ)^bit_offset : F p) + x4_h - y4)
  assert_zero (x6_l * ((2 : ℕ)^bit_offset : F p) + x5_h - y5)
  assert_zero (x7_l * ((2 : ℕ)^bit_offset : F p) + x6_h - y6)
  assert_zero (x0_l * ((2 : ℕ)^bit_offset : F p) + x7_h - y7)
  return { z := ⟨ y0, y1, y2, y3, y4, y5, y6, y7 ⟩ }



def assumptions (input : Inputs (F p)) := input.x.is_normalized

def spec (offset : Fin 64) (input : Inputs (F p)) (out: Outputs (F p)) :=
  let ⟨x⟩ := input
  let ⟨y⟩ := out
  y.value = rot_right64 x.value offset.val

theorem soundness (off : Fin 8) : Soundness (F p) Inputs Outputs (rot64_circuit off) assumptions (spec off) := by
  rintro i0 env ⟨ x0_var, x1_var, x2_var, x3_var, x4_var, x5_var, x6_var, x7_var ⟩ ⟨ x0, x1, x2, x3, x4, x5, x6, x7 ⟩ h_inputs as h

  have h_x0 : x0_var.eval env = x0 := by injections h_inputs
  have h_x1 : x1_var.eval env = x1 := by injections h_inputs
  have h_x2 : x2_var.eval env = x2 := by injections h_inputs
  have h_x3 : x3_var.eval env = x3 := by injections h_inputs
  have h_x4 : x4_var.eval env = x4 := by injections h_inputs
  have h_x5 : x5_var.eval env = x5 := by injections h_inputs
  have h_x6 : x6_var.eval env = x6 := by injections h_inputs
  have h_x7 : x7_var.eval env = x7 := by injections h_inputs
  clear h_inputs

  dsimp only [assumptions, U64.is_normalized] at as
  sorry

def circuit (off : Fin 8) : FormalCircuit (F p) Inputs Outputs where
  main := rot64_circuit off
  assumptions := assumptions
  spec := spec off
  soundness := soundness off
  completeness := by sorry
end Gadgets.Rotation64
