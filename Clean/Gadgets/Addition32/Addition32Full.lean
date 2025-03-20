import Clean.Gadgets.Addition8.Addition8FullCarry
import Clean.Types.U32
import Clean.Gadgets.Addition32.Theorems

namespace Gadgets.Addition32Full
variable {p : ℕ} [Fact p.Prime]
variable [p_large_enough: Fact (p > 512)]

open Provable (field field2 fields)
open FieldUtils (mod_256 floordiv)

structure Inputs (F : Type) where
  x: U32 F
  y: U32 F
  carry_in: F

instance instProvableTypeInputs : ProvableType Inputs where
  size := ProvableType.size U32 + ProvableType.size U32 + 1
  to_elements x :=
    #v[x.x.x0, x.x.x1, x.x.x2, x.x.x3, x.y.x0, x.y.x1, x.y.x2, x.y.x3, x.carry_in]
  from_elements v :=
    let ⟨ .mk [x0, x1, x2, x3, y0, y1, y2, y3, carry_in], _ ⟩ := v
    ⟨ ⟨ x0, x1, x2, x3 ⟩, ⟨ y0, y1, y2, y3 ⟩, carry_in ⟩

structure Outputs (F : Type) where
  z: U32 F
  carry_out: F

instance instProvableTypeOutputs : ProvableType Outputs where
  size := ProvableType.size U32 + 1
  to_elements x := (ProvableType.to_elements x.z) ++ #v[x.carry_out]
  from_elements v :=
    let ⟨ .mk [z0, z1, z2, z3, carry_out], _ ⟩ := v
    ⟨ ⟨ z0, z1, z2, z3 ⟩, carry_out ⟩

open Gadgets.Addition8FullCarry (add8_full_carry)

def add32_full (input : Var Inputs (F p)) : Circuit (F p) (Var Outputs (F p)) := do
  let ⟨x, y, carry_in⟩ := input
  let { z := z0, carry_out := c0 } ← add8_full_carry ⟨ x.x0, y.x0, carry_in ⟩
  let { z := z1, carry_out := c1 } ← add8_full_carry ⟨ x.x1, y.x1, c0 ⟩
  let { z := z2, carry_out := c2 } ← add8_full_carry ⟨ x.x2, y.x2, c1 ⟩
  let { z := z3, carry_out := c3 } ← add8_full_carry ⟨ x.x3, y.x3, c2 ⟩
  return { z := U32.mk z0 z1 z2 z3, carry_out := c3 }

def assumptions (input : Inputs (F p)) :=
  let ⟨x, y, carry_in⟩ := input
  x.is_normalized ∧ y.is_normalized ∧ (carry_in = 0 ∨ carry_in = 1)

def spec (input : Inputs (F p)) (out: Outputs (F p)) :=
  let ⟨x, y, carry_in⟩ := input
  let ⟨z, carry_out⟩ := out
  z.value = (x.value + y.value + carry_in.val) % 2^32
  ∧ carry_out.val = (x.value + y.value + carry_in.val) / 2^32
  ∧ z.is_normalized ∧ (carry_out = 0 ∨ carry_out = 1)

theorem soundness : Soundness (F p) Inputs Outputs add32_full assumptions spec := by
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
  clear h_inputs

  -- -- simplify assumptions
  dsimp only [assumptions, U32.is_normalized] at as

  have ⟨ x_norm, y_norm, carry_in_bool ⟩ := as
  clear as
  have ⟨ x0_byte, x1_byte, x2_byte, x3_byte ⟩ := x_norm
  have ⟨ y0_byte, y1_byte, y2_byte, y3_byte ⟩ := y_norm
  clear x_norm y_norm

  -- -- simplify circuit
  dsimp [add32_full, Boolean.circuit, circuit_norm, Circuit.formal_assertion_to_subcircuit] at h
  simp only [true_implies, true_and, and_assoc] at h
  rw [‹x0_var.eval env = x0›, ‹y0_var.eval env = y0›, ‹carry_in_var.eval env = carry_in›] at h
  rw [‹x1_var.eval env = x1›, ‹y1_var.eval env = y1›] at h
  rw [‹x2_var.eval env = x2›, ‹y2_var.eval env = y2›] at h
  rw [‹x3_var.eval env = x3›, ‹y3_var.eval env = y3›] at h
  repeat clear this
  simp only [constraints_hold_flat, Expression.eval, mul_one, mul_eq_zero, and_true, neg_mul,
    one_mul] at h
  rw [ByteTable.equiv _, ByteTable.equiv _, ByteTable.equiv _, ByteTable.equiv _, Boolean.spec] at h
  repeat rw [add_neg_eq_zero] at h
  set z0 := env.get i0
  set c0 := env.get (i0 + 1)
  set z1 := env.get (i0 + 2)
  set c1 := env.get (i0 + 3)
  set z2 := env.get (i0 + 4)
  set c2 := env.get (i0 + 5)
  set z3 := env.get (i0 + 6)
  set c3 := env.get (i0 + 7)
  have ⟨ z0_byte, c0_bool, h0, z1_byte, c1_bool, h1, z2_byte, c2_bool, h2, z3_byte, c3_bool, h3 ⟩ := h
  clear h

  -- simplify output and spec
  set main := add32_full ⟨⟨ x0_var, x1_var, x2_var, x3_var ⟩,⟨ y0_var, y1_var, y2_var, y3_var ⟩,carry_in_var⟩
  set output := eval env (main.output i0)
  have h_output : output = { z := U32.mk z0 z1 z2 z3, carry_out := c3 } := by
    dsimp [output, circuit_norm]

  rw [h_output]
  dsimp only [spec, U32.value, U32.is_normalized]

  -- get rid of the boolean carry_out and noramlized output
  simp only [c3_bool, z0_byte, z1_byte, z2_byte, z3_byte, and_self, and_true]
  rw [add_neg_eq_iff_eq_add] at h0 h1 h2 h3

  -- apply the main soundness theorem
  apply Gadgets.Addition32.Theorems.add32_soundness
    x0_byte x1_byte x2_byte x3_byte
    y0_byte y1_byte y2_byte y3_byte
    z0_byte z1_byte z2_byte z3_byte
    carry_in_bool c0_bool c1_bool c2_bool c3_bool
    h0 h1 h2 h3


theorem completeness : Completeness (F p) Inputs Outputs add32_full assumptions := by
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
    ⟩ |>.operations i0 |>.local_witnesses env

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
    dsimp [wit, circuit_norm]
    rw [‹x0_var.eval env = x0›, ‹y0_var.eval env = y0›, ‹carry_in_var.eval env = carry_in›,
      ‹x1_var.eval env = x1›, ‹y1_var.eval env = y1›, ‹x2_var.eval env = x2›, ‹y2_var.eval env = y2›,
      ‹x3_var.eval env = x3›, ‹y3_var.eval env = y3›]

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
    rw [(show z0 = wit.get 0 from henv 0), wit.get_eq_lt 0]
    simp only [hwit, List.getElem_cons_zero]
  have hc0 : c0 = floordiv (x0 + y0 + carry_in) 256 := by
    rw [(show c0 = wit.get 1 from henv 1), wit.get_eq_lt 1]
    simp only [hwit, List.getElem_cons_succ, List.getElem_cons_zero]
  have hz1 : z1 = mod_256 (x1 + y1 + c0) := by
    rw [(show z1 = wit.get 2 from henv 2), wit.get_eq_lt 2]
    simp only [hwit, List.getElem_cons_succ, List.getElem_cons_zero]
  have hc1 : c1 = floordiv (x1 + y1 + c0) 256 := by
    rw [(show c1 = wit.get 3 from henv 3), wit.get_eq_lt 3]
    simp only [hwit, List.getElem_cons_succ, List.getElem_cons_zero]
  have hz2 : z2 = mod_256 (x2 + y2 + c1) := by
    rw [(show z2 = wit.get 4 from henv 4), wit.get_eq_lt 4]
    simp only [hwit, List.getElem_cons_succ, List.getElem_cons_zero]
  have hc2 : c2 = floordiv (x2 + y2 + c1) 256 := by
    rw [(show c2 = wit.get 5 from henv 5), wit.get_eq_lt 5]
    simp only [hwit, List.getElem_cons_succ, List.getElem_cons_zero]
  have hz3 : z3 = mod_256 (x3 + y3 + c2) := by
    rw [(show z3 = wit.get 6 from henv 6), wit.get_eq_lt 6]
    simp only [hwit, List.getElem_cons_succ, List.getElem_cons_zero]
  have hc3 : c3 = floordiv (x3 + y3 + c2) 256 := by
    rw [(show c3 = wit.get 7 from henv 7), wit.get_eq_lt 7]
    simp only [hwit, List.getElem_cons_succ, List.getElem_cons_zero]

  -- the add8 completeness proof, four times
  have add8_completeness {x y c_in z c_out : F p}
    (hz: z = mod_256 (x + y + c_in)) (hc_out: c_out = floordiv (x + y + c_in) 256) :
    x.val < 256 → y.val < 256 → c_in = 0 ∨ c_in = 1 →
    ByteTable.contains (#v[z]) ∧ (c_out = 0 ∨ c_out = 1) ∧ x + y + c_in + -1 * z + -1 * (c_out * 256) = 0
  := by
    intro x_byte y_byte hc
    have : z.val < 256 := hz ▸ FieldUtils.mod_256_lt (x + y + c_in)
    use ByteTable.completeness z this
    have carry_lt_2 : c_in.val < 2 := FieldUtils.boolean_lt_2 hc
    have : (x + y + c_in).val < 512 :=
      FieldUtils.byte_sum_and_bit_lt_512 x y c_in x_byte y_byte carry_lt_2
    use (hc_out ▸ FieldUtils.floordiv_bool this)
    rw [FieldUtils.mod_add_div_256 (x + y + c_in), hz, hc_out]
    ring

  have ⟨ z0_byte, c0_bool, h0 ⟩ := add8_completeness hz0 hc0 x0_byte y0_byte carry_in_bool
  have ⟨ z1_byte, c1_bool, h1 ⟩ := add8_completeness hz1 hc1 x1_byte y1_byte c0_bool
  have ⟨ z2_byte, c2_bool, h2 ⟩ := add8_completeness hz2 hc2 x2_byte y2_byte c1_bool
  have ⟨ z3_byte, c3_bool, h3 ⟩ := add8_completeness hz3 hc3 x3_byte y3_byte c2_bool

  exact ⟨ z0_byte, c0_bool, h0, z1_byte, c1_bool, h1, z2_byte, c2_bool, h2, z3_byte, c3_bool, h3 ⟩

def circuit : FormalCircuit (F p) Inputs Outputs where
  main := add32_full
  assumptions := assumptions
  spec := spec
  soundness := soundness
  completeness := completeness

-- lemmas like these can be helpful when using as subcircuit
lemma local_length : ∀ offset input,
  (circuit (p := p)).local_length input offset = 8 := by
  intros; rfl

lemma witness_length : ∀ offset input,
  (Circuit.formal_circuit_to_subcircuit offset
    (circuit (p := p)) input).snd.witness_length = 8 := by
  intros
  apply circuit.local_length_eq
end Gadgets.Addition32Full
