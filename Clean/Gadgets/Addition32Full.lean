import Clean.Gadgets.Addition8.Addition8FullCarry
import Clean.Types.U32

namespace Gadgets.Addition32Full
variable {p : ℕ} [Fact p.Prime]
variable [p_large_enough: Fact (p > 2*2^32)]

open Provable (field field2 fields)
open FieldUtils (mod_256 floordiv)

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

open Gadgets.Addition8FullCarry (add8_full_carry)

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

theorem soundness : Soundness (F p) (Inputs p) (Outputs p) add32_full assumptions spec := by
  rintro i0 env ⟨ x_var, y_var, carry_in_var ⟩ ⟨ x, y, carry_in ⟩ h_inputs as h

  let ⟨ x0, x1, x2, x3 ⟩ := x
  let ⟨ y0, y1, y2, y3 ⟩ := y
  let ⟨ x0_var, x1_var, x2_var, x3_var ⟩ := x_var
  let ⟨ y0_var, y1_var, y2_var, y3_var ⟩ := y_var
  have : x0_var.eval env = x0 := by injections h_inputs
  have : x1_var.eval env = x1 := by injections h_inputs
  have : x2_var.eval env = x2 := by injections h_inputs
  have : x3_var.eval env = x3 := by injections h_inputs
  have : y0_var.eval env = y0 := by injections h_inputs
  have : y1_var.eval env = y1 := by injections h_inputs
  have : y2_var.eval env = y2 := by injections h_inputs
  have : y3_var.eval env = y3 := by injections h_inputs
  have : carry_in_var.eval env = carry_in := by injection h_inputs

  -- -- simplify assumptions
  dsimp only [assumptions, U32.is_normalized] at as

  -- TODO: those are not used because we are assuming right now p > 2^32
  have ⟨ _x_norm, _y_norm, carry_in_bool ⟩ := as
  -- have ⟨ x0_byte, x1_byte, x2_byte, x3_byte ⟩ := x_norm
  -- have ⟨ y0_byte, y1_byte, y2_byte, y3_byte ⟩ := y_norm

  -- -- simplify circuit
  dsimp [add32_full, Boolean.circuit, circuit_norm, Circuit.formal_assertion_to_subcircuit] at h
  simp only [true_implies, true_and, and_assoc] at h
  set z0 := env.get i0
  set c0 := env.get (i0 + 1)
  set z1 := env.get (i0 + 2)
  set c1 := env.get (i0 + 3)
  set z2 := env.get (i0 + 4)
  set c2 := env.get (i0 + 5)
  set z3 := env.get (i0 + 6)
  set c3 := env.get (i0 + 7)
  rw [‹x0_var.eval env = x0›, ‹y0_var.eval env = y0›, ‹carry_in_var.eval env = carry_in›] at h
  rw [‹x1_var.eval env = x1›, ‹y1_var.eval env = y1›] at h
  rw [‹x2_var.eval env = x2›, ‹y2_var.eval env = y2›] at h
  rw [‹x3_var.eval env = x3›, ‹y3_var.eval env = y3›] at h
  rw [ByteTable.equiv z0, ByteTable.equiv z1, ByteTable.equiv z2, ByteTable.equiv z3] at h
  have ⟨ z0_byte, _c0_bool, h0, z1_byte, _c1_bool, h1, z2_byte, _c2_bool, h2, z3_byte, c3_bool, h3 ⟩ := h

  -- simplify output and spec
  set main := add32_full ⟨⟨ x0_var, x1_var, x2_var, x3_var ⟩,⟨ y0_var, y1_var, y2_var, y3_var ⟩,carry_in_var⟩
  set output := eval env (main.output i0)
  have h_output : output = { z := U32.mk z0 z1 z2 z3, carry_out := c3 } := by
    dsimp [output, from_values, to_vars]
    simp only [SubCircuit.witness_length, FlatOperation.witness_length, add_zero]

  rw [h_output]
  dsimp only [spec, U32.value, U32.is_normalized]

  -- -- add up all the equations
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

  exact ⟨ h_low, h_high, ⟨ z0_byte, z1_byte, z2_byte, z3_byte ⟩, c3_bool ⟩

theorem completeness : Completeness (F p) (Inputs p) (Outputs p) add32_full assumptions := by
  rintro i0 env ⟨ x_var, y_var, carry_in_var ⟩ henv  ⟨ x, y, carry_in ⟩ h_inputs as
  let ⟨ x0, x1, x2, x3 ⟩ := x
  let ⟨ y0, y1, y2, y3 ⟩ := y
  let ⟨ x0_var, x1_var, x2_var, x3_var ⟩ := x_var
  let ⟨ y0_var, y1_var, y2_var, y3_var ⟩ := y_var
  have : x0_var.eval env = x0 := by injections
  have : x1_var.eval env = x1 := by injections
  have : x2_var.eval env = x2 := by injections
  have : x3_var.eval env = x3 := by injections
  have : y0_var.eval env = y0 := by injections
  have : y1_var.eval env = y1 := by injections
  have : y2_var.eval env = y2 := by injections
  have : y3_var.eval env = y3 := by injections
  have : carry_in_var.eval env = carry_in := by injections

  -- simplify assumptions
  dsimp [assumptions, U32.is_normalized] at as
  have ⟨ x_norm, y_norm, carry_in_bool ⟩ := as
  have ⟨ x0_byte, x1_byte, x2_byte, x3_byte ⟩ := x_norm
  have ⟨ y0_byte, y1_byte, y2_byte, y3_byte ⟩ := y_norm

  -- simplify circuit
  dsimp [add32_full, Boolean.circuit, Circuit.formal_assertion_to_subcircuit, circuit_norm]
  simp only [true_and, and_assoc]
  rw [‹x0_var.eval env = x0›, ‹y0_var.eval env = y0›, ‹carry_in_var.eval env = carry_in›]
  rw [‹x1_var.eval env = x1›, ‹y1_var.eval env = y1›]
  rw [‹x2_var.eval env = x2›, ‹y2_var.eval env = y2›]
  rw [‹x3_var.eval env = x3›, ‹y3_var.eval env = y3›]

  -- characterize local witnesses
  -- TODO: this is too hard
  let wit : Vector (F p) 8 := add32_full ⟨
    ⟨ x0_var, x1_var, x2_var, x3_var ⟩,
    ⟨ y0_var, y1_var, y2_var, y3_var ⟩,
    carry_in_var
    ⟩ i0 |>.local_witnesses env

  change ∀ i : Fin 8, env.get (i0 + i) = wit.get i at henv

  have hwit : wit.val = [
    mod_256 (x0 + y0 + carry_in),
    floordiv (x0 + y0 + carry_in) 256,
    mod_256 (x1 + y1 + env.get (i0 + 1)),
    floordiv (x1 + y1 + env.get (i0 + 1)) 256,
    mod_256 (x2 + y2 + env.get (i0 + 3)),
    floordiv (x2 + y2 + env.get (i0 + 3)) 256,
    mod_256 (x3 + y3 + env.get (i0 + 5)),
    floordiv (x3 + y3 + env.get (i0 + 5)) 256
  ] := by
    dsimp only [wit]
    -- TODO we need a simp set
    dsimp only [OperationsList.from_offset, Operations.local_witnesses, Vector.append,
      Expression.eval, Circuit.formal_assertion_to_subcircuit, to_flat_operations,
      SubCircuit.witness_length, FlatOperation.witness_length, Operations.local_length, Vector.push,
      SubCircuit.witnesses, FlatOperation.witnesses, Vector.map, List.map, Vector.nil]
    rw [‹x0_var.eval env = x0›, ‹y0_var.eval env = y0›, ‹carry_in_var.eval env = carry_in›,
      ‹x1_var.eval env = x1›, ‹y1_var.eval env = y1›, ‹x2_var.eval env = x2›, ‹y2_var.eval env = y2›,
      ‹x3_var.eval env = x3›, ‹y3_var.eval env = y3›]
    simp only [List.nil_append, List.cons_append]

  set z0 := env.get i0
  set c0 := env.get (i0 + 1)
  set z1 := env.get (i0 + 2)
  set c1 := env.get (i0 + 3)
  set z2 := env.get (i0 + 4)
  set c2 := env.get (i0 + 5)
  set z3 := env.get (i0 + 6)
  set c3 := env.get (i0 + 7)

  -- note: List accesses like `[a, b, c][2] = c` can also be proved by `rfl`,
  -- but that seems slower than simp with getElem lemmas
  have hz0 : z0 = mod_256 (x0 + y0 + carry_in) := by
    rw [(show z0 = wit.get 0 from henv 0), wit.get_eq_lt 0 (by norm_num)]
    simp only [hwit, List.getElem_cons_zero]
  have hc0 : c0 = floordiv (x0 + y0 + carry_in) 256 := by
    rw [(show c0 = wit.get 1 from henv 1), wit.get_eq_lt 1 (by norm_num)]
    simp only [hwit, List.getElem_cons_succ, List.getElem_cons_zero]
  have hz1 : z1 = mod_256 (x1 + y1 + c0) := by
    rw [(show z1 = wit.get 2 from henv 2), wit.get_eq_lt 2 (by norm_num)]
    simp only [hwit, List.getElem_cons_succ, List.getElem_cons_zero]
  have hc1 : c1 = floordiv (x1 + y1 + c0) 256 := by
    rw [(show c1 = wit.get 3 from henv 3), wit.get_eq_lt 3 (by norm_num)]
    simp only [hwit, List.getElem_cons_succ, List.getElem_cons_zero]
  have hz2 : z2 = mod_256 (x2 + y2 + c1) := by
    rw [(show z2 = wit.get 4 from henv 4), wit.get_eq_lt 4 (by norm_num)]
    simp only [hwit, List.getElem_cons_succ, List.getElem_cons_zero]
  have hc2 : c2 = floordiv (x2 + y2 + c1) 256 := by
    rw [(show c2 = wit.get 5 from henv 5), wit.get_eq_lt 5 (by norm_num)]
    simp only [hwit, List.getElem_cons_succ, List.getElem_cons_zero]
  have hz3 : z3 = mod_256 (x3 + y3 + c2) := by
    rw [(show z3 = wit.get 6 from henv 6), wit.get_eq_lt 6 (by norm_num)]
    simp only [hwit, List.getElem_cons_succ, List.getElem_cons_zero]
  have hc3 : c3 = floordiv (x3 + y3 + c2) 256 := by
    rw [(show c3 = wit.get 7 from henv 7), wit.get_eq_lt 7 (by norm_num)]
    simp only [hwit, List.getElem_cons_succ, List.getElem_cons_zero]

  -- the add8 completeness proof, four times
  have add8_completeness {x y c_in z c_out : F p}
    (hz: z = mod_256 (x + y + c_in)) (hc_out: c_out = floordiv (x + y + c_in) 256) :
    x.val < 256 → y.val < 256 → c_in = 0 ∨ c_in = 1 →
    ByteTable.contains (vec [z]) ∧ (c_out = 0 ∨ c_out = 1) ∧ x + y + c_in + -1 * z + -1 * (c_out * 256) = 0
  := by
    intro _ _ hc
    have : z.val < 256 := hz ▸ FieldUtils.mod_256_lt (x + y + c_in)
    use ByteTable.completeness z this
    have : c_in.val < 2 := FieldUtils.boolean_lt_2 hc
    have : (x + y + c_in).val < 512 := by field_to_nat_u32
    use (hc_out ▸ FieldUtils.floordiv_bool this)
    rw [FieldUtils.mod_add_div_256 (x + y + c_in), hz, hc_out]
    ring

  have ⟨ z0_byte, c0_bool, h0 ⟩ := add8_completeness hz0 hc0 x0_byte y0_byte carry_in_bool
  have ⟨ z1_byte, c1_bool, h1 ⟩ := add8_completeness hz1 hc1 x1_byte y1_byte c0_bool
  have ⟨ z2_byte, c2_bool, h2 ⟩ := add8_completeness hz2 hc2 x2_byte y2_byte c1_bool
  have ⟨ z3_byte, c3_bool, h3 ⟩ := add8_completeness hz3 hc3 x3_byte y3_byte c2_bool

  exact ⟨ z0_byte, c0_bool, h0, z1_byte, c1_bool, h1, z2_byte, c2_bool, h2, z3_byte, c3_bool, h3 ⟩

def circuit : FormalCircuit (F p) (Inputs p) (Outputs p) where
  main := add32_full
  assumptions := assumptions
  spec := spec
  soundness := soundness
  completeness := completeness
end Gadgets.Addition32Full
