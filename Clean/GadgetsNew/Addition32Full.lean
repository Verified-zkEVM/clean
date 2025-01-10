import Clean.GadgetsNew.Add8.Addition8FullCarry
import Clean.Types.U32

namespace Addition32Full
variable {p : ℕ} [Fact (p ≠ 0)] [Fact p.Prime]
variable [p_large_enough: Fact (p > 512)]

open Provable (field field2 fields)

structure InputStruct (F : Type) where
  x: U32 F
  y: U32 F
  carry_in: F

def Inputs (p : ℕ) : TypePair := ⟨
  InputStruct (Expression (F p)),
  InputStruct (F p)
⟩

@[simp]
instance : ProvableType (F p) (Inputs p) where
  size := 9 -- 4 + 4 + 1
  to_vars s := vec [s.x.x0, s.x.x1, s.x.x2, s.x.x3, s.y.x0, s.y.x1, s.y.x2, s.y.x3, s.carry_in]
  from_vars v :=
    let ⟨ [x0, x1, x2, x3, y0, y1, y2, y3, carry_in], _ ⟩ := v
    ⟨ ⟨ x0, x1, x2, x3 ⟩, ⟨ y0, y1, y2, y3 ⟩, carry_in ⟩
  to_values s := vec [s.x.x0, s.x.x1, s.x.x2, s.x.x3, s.y.x0, s.y.x1, s.y.x2, s.y.x3, s.carry_in]
  from_values v :=
    let ⟨ [x0, x1, x2, x3, y0, y1, y2, y3, carry_in], _ ⟩ := v
    ⟨ ⟨ x0, x1, x2, x3 ⟩, ⟨ y0, y1, y2, y3 ⟩, carry_in ⟩


structure OutputStruct (F : Type) where
  z: U32 F
  carry_out: F

def Outputs (p : ℕ) : TypePair := ⟨
  OutputStruct (Expression (F p)),
  OutputStruct (F p)
⟩

instance : ProvableType (F p) (Outputs p) where
  size := 5 -- 4 + 1
  to_vars s := vec [s.z.x0, s.z.x1, s.z.x2, s.z.x3, s.carry_out]
  from_vars v :=
    let ⟨ [z0, z1, z2, z3, carry_out], _ ⟩ := v
    ⟨ ⟨ z0, z1, z2, z3 ⟩, carry_out ⟩
  to_values s := vec [s.z.x0, s.z.x1, s.z.x2, s.z.x3, s.carry_out]
  from_values v :=
    let ⟨ [z0, z1, z2, z3, carry_out], _ ⟩ := v
    ⟨ ⟨ z0, z1, z2, z3 ⟩, carry_out ⟩

def add32_full (input : (Inputs p).var) : Circuit (F p) (Outputs p).var := do
  let ⟨x, y, carry_in⟩ := input

  let {
    z := z0,
    carry_out := c0
  } ← subcircuit Add8FullCarry.circuit ⟨ x.x0, y.x0, carry_in ⟩

  let {
    z := z1,
    carry_out := c1
  } ← subcircuit Add8FullCarry.circuit ⟨ x.x1, y.x1, c0 ⟩

  let {
    z := z2,
    carry_out := c2
  } ← subcircuit Add8FullCarry.circuit ⟨ x.x2, y.x2, c1 ⟩

  let {
    z := z3,
    carry_out := c3
  } ← subcircuit Add8FullCarry.circuit ⟨ x.x3, y.x3, c2 ⟩

  return {
    z := U32.mk z0 z1 z2 z3,
    carry_out := c3
  }

def assumptions (input : (Inputs p).value) :=
  let ⟨x, y, carry_in⟩ := input
  x.is_normalized ∧ y.is_normalized ∧ (carry_in = 0 ∨ carry_in = 1)

def spec (input : (Inputs p).value) (out: (Outputs p).value) :=
  let ⟨x, y, carry_in⟩ := input
  let ⟨z, carry_out⟩ := out
  z.value = (x.value + y.value + carry_in.val) % 2^32 ∧
  z.is_normalized ∧
  carry_out.val = (x.value + y.value + carry_in.val) / 2^32

def circuit : FormalCircuit (F p) (Inputs p) (Outputs p) where
  main := add32_full
  assumptions := assumptions
  spec := spec
  soundness := by
    rintro ctx env ⟨ x, y, carry_in ⟩ ⟨ x_var, y_var, carry_in_var ⟩ h_inputs as h
    let ⟨ x0, x1, x2, x3 ⟩ := x
    let ⟨ y0, y1, y2, y3 ⟩ := y
    let ⟨ x0_var, x1_var, x2_var, x3_var ⟩ := x_var
    let ⟨ y0_var, y1_var, y2_var, y3_var ⟩ := y_var
    have : x0_var.eval_env env = x0 := by injection h_inputs with x; injection x
    have : x1_var.eval_env env = x1 := by injection h_inputs with x; injection x
    have : x2_var.eval_env env = x2 := by injection h_inputs with x; injection x
    have : x3_var.eval_env env = x3 := by injection h_inputs with x; injection x
    have : y0_var.eval_env env = y0 := by injection h_inputs with _ y; injection y
    have : y1_var.eval_env env = y1 := by injection h_inputs with _ y; injection y
    have : y2_var.eval_env env = y2 := by injection h_inputs with _ y; injection y
    have : y3_var.eval_env env = y3 := by injection h_inputs with _ y; injection y
    have : carry_in_var.eval_env env = carry_in := by injection h_inputs

    -- simplify assumptions
    dsimp [assumptions, U32.is_normalized] at as
    have ⟨ x_norm, y_norm, carry_in_bool ⟩ := as
    have ⟨ x0_byte, x1_byte, x2_byte, x3_byte ⟩ := x_norm
    have ⟨ y0_byte, y1_byte, y2_byte, y3_byte ⟩ := y_norm

    -- simplify first subcircuit
    have h0 := h.left
    let i0 := ctx.offset
    have : ctx.offset = i0 := rfl
    let i1 := i0 + 1
    let z0 := env i0
    let c0 := env i1
    dsimp [Add8FullCarry.circuit, Add8FullCarry.spec, Add8FullCarry.assumptions] at h0
    rw [‹x0_var.eval_env env = x0›, ‹y0_var.eval_env env = y0›, ‹carry_in_var.eval_env env = carry_in›] at h0
    rw [‹ctx.offset = i0›, (by rfl: env i0 = z0), (by rfl : env (i0 + 1) = c0)] at h0
    specialize h0 ⟨ x0_byte, y0_byte, carry_in_bool ⟩

    -- simplify second subcircuit
    have h1 := h.right.left
    let i2 := i0 + 2
    let i3 := i0 + 3
    let z1 := env i2
    let c1 := env i3
    dsimp [Add8FullCarry.circuit, Add8FullCarry.spec, Add8FullCarry.assumptions] at h1
    rw [‹x1_var.eval_env env = x1›, ‹y1_var.eval_env env = y1›] at h1
    rw [‹ctx.offset = i0›, (by rfl : env (i0 + 1) = c0), (by rfl: env i2 = z1), (by rfl : env (i2 + 1) = c1)] at h1
    have c0_bool : c0 = 0 ∨ c0 = 1 := by sorry
    specialize h1 ⟨ x1_byte, y1_byte, c0_bool ⟩

    -- simplify third subcircuit
    have h2 := h.right.right.left
    let i4 := i0 + 4
    let i5 := i0 + 5
    let z2 := env i4
    let c2 := env i5
    dsimp [Add8FullCarry.circuit, Add8FullCarry.spec, Add8FullCarry.assumptions] at h2
    rw [‹x2_var.eval_env env = x2›, ‹y2_var.eval_env env = y2›] at h2
    rw [‹ctx.offset = i0›, (by rfl : env (i2 + 1) = c1), (by rfl: env i4 = z2), (by rfl : env (i4 + 1) = c2)] at h2
    have c1_bool : c1 = 0 ∨ c1 = 1 := by sorry
    specialize h2 ⟨ x2_byte, y2_byte, c1_bool ⟩

    -- simplify fourth subcircuit
    have h3 := h.right.right.right
    let i6 := i0 + 6
    let i7 := i0 + 7
    let z3 := env i6
    let c3 := env i7
    dsimp [Add8FullCarry.circuit, Add8FullCarry.spec, Add8FullCarry.assumptions] at h3
    rw [‹x3_var.eval_env env = x3›, ‹y3_var.eval_env env = y3›] at h3
    rw [‹ctx.offset = i0›, (by rfl : env (i4 + 1) = c2), (by rfl: env i6 = z3), (by rfl : env (i6 + 1) = c3)] at h3
    have c2_bool : c2 = 0 ∨ c2 = 1 := by sorry
    specialize h3 ⟨ x3_byte, y3_byte, c2_bool ⟩
    sorry

  completeness := by
    sorry
end Addition32Full
