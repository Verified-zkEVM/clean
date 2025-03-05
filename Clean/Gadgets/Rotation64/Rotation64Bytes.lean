import Clean.Gadgets.Addition8.Addition8FullCarry
import Clean.Types.U64
import Clean.Gadgets.Rotation64.Theorems

namespace Gadgets.Rotation64Bytes
variable {p : ℕ} [Fact p.Prime]
variable [p_large_enough: Fact (p > 512)]

open Gadgets.Rotation64.Theorems (rot_right64)

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
  Rotate the 64-bit integer by increments of 8 positions
  This gadget does not introduce constraints
-/
def rot64_bytes (offset : Fin 8) (input : (Inputs p).var) : Circuit (F p) (Outputs p).var := do
  let ⟨x0, x1, x2, x3 , x4, x5, x6, x7⟩ := input
  let offset := offset.val

  if offset = 0 then
    return ⟨ x0, x1, x2, x3, x4, x5, x6, x7 ⟩
  else if offset = 1 then
    return ⟨ x1, x2, x3, x4, x5, x6, x7, x0 ⟩
  else if offset = 2 then
    return ⟨ x2, x3, x4, x5, x6, x7, x0, x1 ⟩
  else if offset = 3 then
    return ⟨ x3, x4, x5, x6, x7, x0, x1, x2 ⟩
  else if offset = 4 then
    return ⟨ x4, x5, x6, x7, x0, x1, x2, x3 ⟩
  else if offset = 5 then
    return ⟨ x5, x6, x7, x0, x1, x2, x3, x4 ⟩
  else if offset = 6 then
    return ⟨ x6, x7, x0, x1, x2, x3, x4, x5 ⟩
  else
    return ⟨ x7, x0, x1, x2, x3, x4, x5, x6 ⟩

def assumptions (input : (Inputs p).value) := input.x.is_normalized

def spec (offset : Fin 8) (input : (Inputs p).value) (out: (Outputs p).value) :=
  let ⟨x⟩ := input
  let ⟨y⟩ := out
  y.value = rot_right64 x.value (offset.val * 8)

theorem soundness (off : Fin 8) : Soundness (F p) (Inputs p) (Outputs p) (rot64_bytes off) assumptions (spec off) := by
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
  clear h

  dsimp only [assumptions, U64.is_normalized] at as
  fin_cases off
  · simp [circuit_norm, rot64_bytes, spec, circuit_norm, Circuit.output, pure]
    rw [h_x0, h_x1, h_x2, h_x3, h_x4, h_x5, h_x6, h_x7]
    simp [U64.value, rot_right64, Nat.mod_one]

  · simp [circuit_norm, rot64_bytes, spec, circuit_norm, Circuit.output, pure]
    rw [h_x0, h_x1, h_x2, h_x3, h_x4, h_x5, h_x6, h_x7]
    simp only [U64.value, rot_right64]
    rw [
      show (8%64) = 8 by norm_num,
      show (64 - 8) = 56 by norm_num,
    ]
    have x0_pos : 0 ≤ x0.val := by exact Nat.zero_le _
    zify at *
    set x0 : ℤ := x0.val.cast
    set x1 : ℤ := x1.val.cast
    set x2 : ℤ := x2.val.cast
    set x3 : ℤ := x3.val.cast
    set x4 : ℤ := x4.val.cast
    set x5 : ℤ := x5.val.cast
    set x6 : ℤ := x6.val.cast
    set x7 : ℤ := x7.val.cast


    have h : (x0 + x1 * 256 + x2 * 256 ^ 2 + x3 * 256 ^ 3 + x4 * 256 ^ 4 + x5 * 256 ^ 5 + x6 * 256 ^ 6 + x7 * 256 ^ 7) % 2 ^ 8 = x0 := by
      repeat
        norm_num
        rw [Int.add_emod, Int.mul_emod]
        try rw [show ((72057594037927936 : ℤ) % 256) = 0 by rfl]
        try rw [show ((281474976710656 : ℤ) % 256) = 0 by rfl]
        try rw [show ((1099511627776 : ℤ) % 256) = 0 by rfl]
        try rw [show ((4294967296 : ℤ) % 256) = 0 by rfl]
        try rw [show ((16777216 : ℤ) % 256) = 0 by rfl]
        try rw [show ((65536 : ℤ) % 256) = 0 by rfl]
        norm_num
      rw [←Int.mod_eq_emod x0_pos (by norm_num), Int.mod_eq_of_lt x0_pos (by simp only [as])]


    have h' : (x0 + x1 * 256 + x2 * 256 ^ 2 + x3 * 256 ^ 3 + x4 * 256 ^ 4 + x5 * 256 ^ 5 + x6 * 256 ^ 6 + x7 * 256 ^ 7) / 2 ^ 8 =
        x1 + x2 * 256 + x3 * 256 ^ 2 + x4 * 256 ^ 3 + x5 * 256 ^ 4 + x6 * 256 ^ 5 + x7 * 256 ^ 6 := by

      repeat
        norm_num
        rw [Int.add_ediv_of_dvd_right (by
          rw [Int.dvd_iff_emod_eq_zero, Int.mul_emod]
          try rw [show ((72057594037927936 : ℤ) % 256) = 0 by rfl]
          try rw [show ((281474976710656 : ℤ) % 256) = 0 by rfl]
          try rw [show ((1099511627776 : ℤ) % 256) = 0 by rfl]
          try rw [show ((4294967296 : ℤ) % 256) = 0 by rfl]
          try rw [show ((16777216 : ℤ) % 256) = 0 by rfl]
          try rw [show ((65536 : ℤ) % 256) = 0 by rfl]
          try rw [show ((256 : ℤ) % 256) = 0 by rfl]
          rfl)]
        rw [Int.mul_ediv_assoc _ (by norm_num)]
        norm_num
      rw [Int.ediv_eq_zero_of_lt (by simp only [x0_pos]) (by simp only [as])]

    rw [h, h']
    ring


  repeat sorry

def circuit (off : Fin 8) : FormalCircuit (F p) (Inputs p) (Outputs p) where
  main := rot64_bytes off
  assumptions := assumptions
  spec := spec off
  soundness := soundness off
  completeness := by sorry
end Gadgets.Rotation64Bytes
