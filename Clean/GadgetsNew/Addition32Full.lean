import Clean.GadgetsNew.Add8.Addition8FullCarry
import Clean.Types.U32

namespace Addition32Full
variable {p : ℕ} [Fact (p ≠ 0)] [Fact p.Prime]
variable [p_large_enough: Fact (p > 2*2^32)]

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

open Add8FullCarry (add8_full_carry)

def add32_full (input : (Inputs p).var) : Circuit (F p) (Outputs p).var := do
  let ⟨x, y, carry_in⟩ := input
  let { z := z0, carry_out := c0 } ← add8_full_carry ⟨ x.x0, y.x0, carry_in ⟩
  let { z := z1, carry_out := c1 } ← add8_full_carry ⟨ x.x1, y.x1, c0 ⟩
  let { z := z2, carry_out := c2 } ← add8_full_carry ⟨ x.x2, y.x2, c1 ⟩
  let { z := z3, carry_out := c3 } ← add8_full_carry ⟨ x.x3, y.x3, c2 ⟩
  return { z := U32.mk z0 z1 z2 z3, carry_out := c3 }

def assumptions (input : (Inputs p).value) :=
  let ⟨x, y, carry_in⟩ := input
  x.is_normalized ∧ y.is_normalized ∧ (carry_in = 0 ∨ carry_in = 1)

def spec (input : (Inputs p).value) (out: (Outputs p).value) :=
  let ⟨x, y, carry_in⟩ := input
  let ⟨z, carry_out⟩ := out
  z.value = (x.value + y.value + carry_in.val) % 2^32
  ∧ carry_out.val = (x.value + y.value + carry_in.val) / 2^32
  ∧ z.is_normalized ∧ (carry_out = 0 ∨ carry_out = 1)

set_option linter.unusedVariables false

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
    have : x0_var.eval_env env = x0 := by injections
    have : x1_var.eval_env env = x1 := by injections
    have : x2_var.eval_env env = x2 := by injections
    have : x3_var.eval_env env = x3 := by injections
    have : y0_var.eval_env env = y0 := by injections
    have : y1_var.eval_env env = y1 := by injections
    have : y2_var.eval_env env = y2 := by injections
    have : y3_var.eval_env env = y3 := by injections
    have : carry_in_var.eval_env env = carry_in := by injection h_inputs

    -- simplify assumptions
    dsimp [assumptions, U32.is_normalized] at as
    have ⟨ x_norm, y_norm, carry_in_bool ⟩ := as
    have ⟨ x0_byte, x1_byte, x2_byte, x3_byte ⟩ := x_norm
    have ⟨ y0_byte, y1_byte, y2_byte, y3_byte ⟩ := y_norm

    -- simplify circuit
    dsimp [add32_full, Boolean.circuit, Circuit.formal_assertion_to_subcircuit] at h
    set i0 := ctx.offset
    have : ctx.offset = i0 := rfl
    set z0 := env i0
    set c0 := env (i0 + 1)
    set z1 := env (i0 + 2)
    set c1 := env (i0 + 3)
    set z2 := env (i0 + 4)
    set c2 := env (i0 + 5)
    set z3 := env (i0 + 6)
    set c3 := env (i0 + 7)
    rw [‹x0_var.eval_env env = x0›, ‹y0_var.eval_env env = y0›, ‹carry_in_var.eval_env env = carry_in›] at h
    rw [‹x1_var.eval_env env = x1›, ‹y1_var.eval_env env = y1›] at h
    rw [‹x2_var.eval_env env = x2›, ‹y2_var.eval_env env = y2›] at h
    rw [‹x3_var.eval_env env = x3›, ‹y3_var.eval_env env = y3›] at h
    rw [ByteTable.equiv z0, ByteTable.equiv z1, ByteTable.equiv z2, ByteTable.equiv z3] at h
    simp only [true_implies] at h
    have ⟨ z0_byte, c0_bool, h0, z1_byte, c1_bool, h1, z2_byte, c2_bool, h2, z3_byte, c3_bool, h3 ⟩ := h

    -- simplify spec
    dsimp [spec, U32.value, U32.is_normalized]
    rw [‹ctx.offset = i0›, (by rfl: env (i0 + 7) = c3)]
    rw [(by rfl: env i0 = z0), (by rfl: env (i0 + 2) = z1), (by rfl: env (i0 + 4) = z2), (by rfl: env (i0 + 6) = z3)]

    -- add up all the equations
    let z := z0 + z1*256 + z2*256^2 + z3*256^3
    let x := x0 + x1*256 + x2*256^2 + x3*256^3
    let y := y0 + y1*256 + y2*256^2 + y3*256^3
    let lhs := z + c3*2^32
    let rhs₀ := x0 + y0 + carry_in + -1 * z0 + -1 * (c0 * 256) -- h0 expression
    let rhs₁ := x1 + y1 + c0 + -1 * z1 + -1 * (c1 * 256) -- h1 expression
    let rhs₂ := x2 + y2 + c1 + -1 * z2 + -1 * (c2 * 256) -- h2 expression
    let rhs₃ := x3 + y3 + c2 + -1 * z3 + -1 * (c3 * 256) -- h3 expression

    have h_add := calc z + c3*2^32
      -- substitute equations
      _ = lhs + 0 + 256*0 + 256^2*0 + 256^3*0 := by ring
      _ = lhs + rhs₀ + 256*rhs₁ + 256^2*rhs₂ + 256^3*rhs₃ := by dsimp [rhs₀, rhs₁, rhs₂, rhs₃]; rw [h0, h1, h2, h3]
      -- simplify
      _ = x + y + carry_in := by ring

    -- move added equation into Nat
    let z_nat := z0.val + z1.val*256 + z2.val*256^2 + z3.val*256^3
    let x_nat := x0.val + x1.val*256 + x2.val*256^2 + x3.val*256^3
    let y_nat := y0.val + y1.val*256 + y2.val*256^2 + y3.val*256^3

    have : c3.val < 2 := FieldUtils.boolean_lt_2 c3_bool
    have : carry_in.val < 2 := FieldUtils.boolean_lt_2 carry_in_bool

    have h_add_nat := calc z_nat + c3.val*2^32
      _ = (z + c3*2^32).val := by dsimp only [z_nat]; field_to_nat_u32
      _ = (x + y + carry_in).val := congrArg ZMod.val h_add
      _ = x_nat + y_nat + carry_in.val := by dsimp only [x_nat, y_nat]; field_to_nat_u32

    -- show that lhs splits into low and high 32 bits
    have : z_nat < 2^32 := by dsimp only [z_nat]; linarith

    have h_low : z_nat = (x_nat + y_nat + carry_in.val) % 2^32 := by
      suffices h : z_nat = z_nat % 2^32 by
        rw [← h_add_nat, ← Nat.add_mod_mod, ← Nat.mul_mod_mod]
        simpa using h
      rw [Nat.mod_eq_of_lt ‹z_nat < 2^32›]

    have h_high : c3.val = (x_nat + y_nat + carry_in.val) / 2^32 := by
      rw [← h_add_nat, Nat.add_mul_div_right _ _ (by norm_num)]
      rw [Nat.div_eq_of_lt ‹z_nat < 2^32›, zero_add]

    use h_low
    use h_high
    use ⟨ z0_byte, z1_byte, z2_byte, z3_byte ⟩
    use c3_bool

  completeness := by
    rintro ctx ⟨ x, y, carry_in ⟩ ⟨ x_var, y_var, carry_in_var ⟩ h_inputs as
    let ⟨ x0, x1, x2, x3 ⟩ := x
    let ⟨ y0, y1, y2, y3 ⟩ := y
    let ⟨ x0_var, x1_var, x2_var, x3_var ⟩ := x_var
    let ⟨ y0_var, y1_var, y2_var, y3_var ⟩ := y_var
    have : x0_var.eval = x0 := by injections
    have : x1_var.eval = x1 := by injections
    have : x2_var.eval = x2 := by injections
    have : x3_var.eval = x3 := by injections
    have : y0_var.eval = y0 := by injections
    have : y1_var.eval = y1 := by injections
    have : y2_var.eval = y2 := by injections
    have : y3_var.eval = y3 := by injections
    have : carry_in_var.eval = carry_in := by injections

    -- simplify assumptions
    dsimp [assumptions, U32.is_normalized] at as
    have ⟨ x_norm, y_norm, carry_in_bool ⟩ := as
    have ⟨ x0_byte, x1_byte, x2_byte, x3_byte ⟩ := x_norm
    have ⟨ y0_byte, y1_byte, y2_byte, y3_byte ⟩ := y_norm

    -- simplify circuit
    dsimp [add32_full, Boolean.circuit, Circuit.formal_assertion_to_subcircuit]
    rw [‹x0_var.eval = x0›, ‹y0_var.eval = y0›, ‹carry_in_var.eval = carry_in›]
    rw [‹x1_var.eval = x1›, ‹y1_var.eval = y1›]
    rw [‹x2_var.eval = x2›, ‹y2_var.eval = y2›]
    rw [‹x3_var.eval = x3›, ‹y3_var.eval = y3›]
    set z0 := FieldUtils.mod_256 (x0 + y0 + carry_in)
    set c0 := FieldUtils.floordiv (x0 + y0 + carry_in) 256
    set z1 := FieldUtils.mod_256 (x1 + y1 + c0)
    set c1 := FieldUtils.floordiv (x1 + y1 + c0) 256
    set z2 := FieldUtils.mod_256 (x2 + y2 + c1)
    set c2 := FieldUtils.floordiv (x2 + y2 + c1) 256
    set z3 := FieldUtils.mod_256 (x3 + y3 + c2)
    set c3 := FieldUtils.floordiv (x3 + y3 + c2) 256

    simp only [true_and]

    -- the add8 completeness proof, four times
    have add8_completeness {x y c_in : F p} :
      let z := FieldUtils.mod_256 (x + y + c_in);
      let c_out := FieldUtils.floordiv (x + y + c_in) 256;
      x.val < 256 → y.val < 256 → c_in = 0 ∨ c_in = 1 →
      ByteTable.contains (vec [z]) ∧ (c_out = 0 ∨ c_out = 1) ∧ x + y + c_in + -1 * z + -1 * (c_out * 256) = 0
    := by
      intro z c_out _ _ hc
      have : z.val < 256 := FieldUtils.mod_256_lt (x + y + c_in)
      use ByteTable.completeness z this
      have : c_in.val < 2 := FieldUtils.boolean_lt_2 hc
      have : (x + y + c_in).val < 512 := by field_to_nat_u32
      use FieldUtils.floordiv_bool this
      rw [FieldUtils.mod_add_div_256 (x + y + c_in)]
      ring

    have ⟨ z0_byte, c0_bool, h0 ⟩ := add8_completeness x0_byte y0_byte carry_in_bool
    have ⟨ z1_byte, c1_bool, h1 ⟩ := add8_completeness x1_byte y1_byte c0_bool
    have ⟨ z2_byte, c2_bool, h2 ⟩ := add8_completeness x2_byte y2_byte c1_bool
    have ⟨ z3_byte, c3_bool, h3 ⟩ := add8_completeness x3_byte y3_byte c2_bool
    exact ⟨ z0_byte, c0_bool, h0, z1_byte, c1_bool, h1, z2_byte, c2_bool, h2, z3_byte, c3_bool, h3 ⟩
end Addition32Full
