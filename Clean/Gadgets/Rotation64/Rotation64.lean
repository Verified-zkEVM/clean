import Clean.Types.U64
import Clean.Gadgets.Rotation64.Theorems
import Clean.Gadgets.Rotation64.Rotation64Bytes

namespace Gadgets.Rotation64
variable {p : ℕ} [Fact p.Prime]
variable [p_large_enough: Fact (p > 512)]

open Gadgets.Rotation64.Theorems (rot_right64 rot_right8)

structure InputStruct (F : Type) where
  x: U64 F

instance (F : Type) : StructuredElements InputStruct F where
  size := StructuredElements.size U64 F
  to_elements x := (StructuredElements.to_elements x.x)
  from_elements v :=
    let ⟨ [x0, x1, x2, x3, x4, x5, x6, x7], _ ⟩ := v
    ⟨ ⟨ x0, x1, x2, x3, x4, x5, x6, x7 ⟩ ⟩

def Inputs (p : ℕ) : TypePair := ⟨
  InputStruct (Expression (F p)),
  InputStruct (F p)
⟩

@[simp]
instance : ProvableType (F p) (Inputs p) where
  size := 8
  to_vars s := vec [s.x.x0, s.x.x1, s.x.x2, s.x.x3, s.x.x4, s.x.x5, s.x.x6, s.x.x7]
  from_vars v :=
    let ⟨ [x0, x1, x2, x3, x4, x5, x6, x7], _ ⟩ := v
    ⟨ ⟨ x0, x1, x2, x3, x4, x5, x6, x7 ⟩ ⟩
  to_values s := vec [s.x.x0, s.x.x1, s.x.x2, s.x.x3, s.x.x4, s.x.x5, s.x.x6, s.x.x7]
  from_values v :=
    let ⟨ [x0, x1, x2, x3, x4, x5, x6, x7], _ ⟩ := v
    ⟨ ⟨ x0, x1, x2, x3, x4, x5, x6, x7 ⟩ ⟩


structure OutputStruct (F : Type) where
  z: U64 F

instance (F : Type) : StructuredElements OutputStruct F where
  size := StructuredElements.size U64 F
  to_elements x := (StructuredElements.to_elements x.z)
  from_elements v :=
    let ⟨ [z0, z1, z2, z3, z4, z5, z6, z7], _ ⟩ := v
    ⟨ ⟨ z0, z1, z2, z3, z4, z5, z6, z7 ⟩ ⟩

def Outputs (p : ℕ) : TypePair := ⟨
  OutputStruct (Expression (F p)),
  OutputStruct (F p)
⟩

instance : ProvableType (F p) (Outputs p) where
  size := 8
  to_vars s := vec [s.z.x0, s.z.x1, s.z.x2, s.z.x3, s.z.x4, s.z.x5, s.z.x6, s.z.x7]
  from_vars v :=
    let ⟨ [z0, z1, z2, z3, z4, z5, z6, z7], _ ⟩ := v
    ⟨ ⟨ z0, z1, z2, z3, z4, z5, z6, z7 ⟩ ⟩
  to_values s := vec [s.z.x0, s.z.x1, s.z.x2, s.z.x3, s.z.x4, s.z.x5, s.z.x6, s.z.x7]
  from_values v :=
    let ⟨ [z0, z1, z2, z3, z4, z5, z6, z7], _ ⟩ := v
    ⟨ ⟨ z0, z1, z2, z3, z4, z5, z6, z7 ⟩ ⟩


/--
  Rotate the 64-bit integer by `offset` bits
-/
def rot64_circuit (offset : Fin 64) (input : (Inputs p).var) : Circuit (F p) (Outputs p).var := do
  let byte_offset := offset / 8
  let bit_offset : ℕ := (offset % 8).val

  let x := input.x

  -- apply the byte rotation
  let ⟨out⟩ ← subcircuit (Gadgets.Rotation64Bytes.circuit byte_offset) { x }

  -- apply the bit rotation
  let ⟨x0, x1, x2, x3, x4, x5, x6, x7⟩ := out
  let ⟨z0, z1, z2, z3, z4, z5, z6, z7⟩ ← U64.witness (fun env => U64.mk 0 0 0 0 0 0 0 0)

  let bit_offset_fp : F p := 2 ^ bit_offset
  let bit_offset_fp' : F p := 2 ^ (8 - bit_offset)




  return { z := ⟨ z0, z1, z2, z3, z4, z5, z6, z7 ⟩ }

def assumptions (input : (Inputs p).value) := input.x.is_normalized



def spec (offset : Fin 64) (input : (Inputs p).value) (out: (Outputs p).value) :=
  let ⟨x⟩ := input
  let ⟨y⟩ := out
  y.value = rot_right64 x.value offset.val

theorem soundness (off : Fin 8) : Soundness (F p) (Inputs p) (Outputs p) (rot64_circuit off) assumptions (spec off) := by
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

def circuit (off : Fin 8) : FormalCircuit (F p) (Inputs p) (Outputs p) where
  main := rot64_circuit off
  assumptions := assumptions
  spec := spec off
  soundness := soundness off
  completeness := by sorry
end Gadgets.Rotation64
