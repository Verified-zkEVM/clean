import Clean.Types.U64
import Clean.Circuit.SubCircuit
import Clean.Gadgets.Rotation64.Theorems
import Clean.Gadgets.Rotation64.Rotation64Bytes
import Clean.Gadgets.Rotation64.ByteRotationTable
import Clean.Gadgets.ByteDecomposition
import Clean.Circuit.Provable

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
    let ⟨ .mk [x0, x1, x2, x3, x4, x5, x6, x7], _ ⟩ := v
    ⟨ ⟨ x0, x1, x2, x3, x4, x5, x6, x7 ⟩ ⟩

structure Outputs (F : Type) where
  z: U64 F

instance instProvableTypeOutputs : ProvableType Outputs where
  size := ProvableType.size U64
  to_elements x := (ProvableType.to_elements x.z)
  from_elements v :=
    let ⟨ .mk [z0, z1, z2, z3, z4, z5, z6, z7], _ ⟩ := v
    ⟨ ⟨ z0, z1, z2, z3, z4, z5, z6, z7 ⟩ ⟩


/--
  Rotate the 64-bit integer by `offset` bits
-/
def rot64 (offset : Fin 64) (input : Var Inputs (F p)) : Circuit (F p) (Var Outputs (F p)) := do
  let byte_offset := offset / 8
  let bit_offset : ℕ := (offset % 8).val

  let x := input.x

  -- apply the byte rotation
  let ⟨out⟩ ← subcircuit (Gadgets.Rotation64Bytes.circuit byte_offset) { x }

  -- apply the bit rotation
  let ⟨x0, x1, x2, x3, x4, x5, x6, x7⟩ := out

  let ⟨x0_l, x0_h⟩ ← subcircuit (Gadgets.ByteDecomposition.circuit bit_offset) ⟨x0⟩
  let ⟨x1_l, x1_h⟩ ← subcircuit (Gadgets.ByteDecomposition.circuit bit_offset) ⟨x1⟩
  let ⟨x2_l, x2_h⟩ ← subcircuit (Gadgets.ByteDecomposition.circuit bit_offset) ⟨x2⟩
  let ⟨x3_l, x3_h⟩ ← subcircuit (Gadgets.ByteDecomposition.circuit bit_offset) ⟨x3⟩
  let ⟨x4_l, x4_h⟩ ← subcircuit (Gadgets.ByteDecomposition.circuit bit_offset) ⟨x4⟩
  let ⟨x5_l, x5_h⟩ ← subcircuit (Gadgets.ByteDecomposition.circuit bit_offset) ⟨x5⟩
  let ⟨x6_l, x6_h⟩ ← subcircuit (Gadgets.ByteDecomposition.circuit bit_offset) ⟨x6⟩
  let ⟨x7_l, x7_h⟩ ← subcircuit (Gadgets.ByteDecomposition.circuit bit_offset) ⟨x7⟩

  let ⟨y0, y1, y2, y3, y4, y5, y6, y7⟩ ← subcircuit (U64.witness.circuit (fun _env => U64.mk 0 0 0 0 0 0 0 0)) ⟨⟩

  assert_zero (x1_l * ((2 : ℕ)^(8 - bit_offset) : F p) + x0_h - y0)
  assert_zero (x2_l * ((2 : ℕ)^(8 - bit_offset) : F p) + x1_h - y1)
  assert_zero (x3_l * ((2 : ℕ)^(8 - bit_offset) : F p) + x2_h - y2)
  assert_zero (x4_l * ((2 : ℕ)^(8 - bit_offset) : F p) + x3_h - y3)
  assert_zero (x5_l * ((2 : ℕ)^(8 - bit_offset) : F p) + x4_h - y4)
  assert_zero (x6_l * ((2 : ℕ)^(8 - bit_offset) : F p) + x5_h - y5)
  assert_zero (x7_l * ((2 : ℕ)^(8 - bit_offset) : F p) + x6_h - y6)
  assert_zero (x0_l * ((2 : ℕ)^(8 - bit_offset) : F p) + x7_h - y7)
  return { z := ⟨ y0, y1, y2, y3, y4, y5, y6, y7 ⟩ }

def assumptions (input : Inputs (F p)) := input.x.is_normalized

def spec (offset : Fin 64) (input : Inputs (F p)) (out: Outputs (F p)) :=
  let ⟨x⟩ := input
  let ⟨y⟩ := out
  y.value = rot_right64 x.value offset.val

def circuit (off : Fin 8) : FormalCircuit (F p) Inputs Outputs where
  main := rot64 off
  assumptions := assumptions
  spec := spec off
  soundness := by sorry
  completeness := by sorry
  local_length := 16
  output := sorry
  initial_offset_eq := by
    intros
    fin_cases off
    repeat sorry
  local_length_eq := by
    intros
    fin_cases off
    repeat sorry
  output_eq := by
    intros
    fin_cases off
    repeat sorry

end Gadgets.Rotation64
