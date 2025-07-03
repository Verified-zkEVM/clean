import Clean.Gadgets.Addition8.Addition8FullCarry
import Clean.Types.U32
import Clean.Gadgets.Addition32.Theorems
import Clean.Utils.Primes

namespace Gadgets.Addition32Full
variable {p : ℕ} [Fact p.Prime] [Fact (p > 512)]

open ByteUtils (mod256 floorDiv256)

structure Inputs (F : Type) where
  x: U32 F
  y: U32 F
  carry_in: F

instance : ProvableStruct Inputs where
  components := [U32, U32, field]
  toComponents := fun {x, y, carry_in} => .cons x ( .cons y ( .cons carry_in .nil))
  fromComponents := fun (.cons x ( .cons y ( .cons carry_in .nil))) => ⟨ x, y, carry_in ⟩

structure Outputs (F : Type) where
  z: U32 F
  carry_out: F
deriving Repr

instance : ProvableStruct Outputs where
  components := [U32, field]
  toComponents := fun {z, carry_out} => .cons z ( .cons carry_out .nil)
  fromComponents := fun (.cons z ( .cons carry_out .nil)) => ⟨ z, carry_out ⟩


def main (input : Var Inputs (F p)) : Circuit (F p) (Var Outputs (F p)) := do
  let ⟨x, y, carry_in⟩ := input
  let { z := z0, carry_out := c0 } ← Addition8FullCarry.main ⟨ x.x0, y.x0, carry_in ⟩
  let { z := z1, carry_out := c1 } ← Addition8FullCarry.main ⟨ x.x1, y.x1, c0 ⟩
  let { z := z2, carry_out := c2 } ← Addition8FullCarry.main ⟨ x.x2, y.x2, c1 ⟩
  let { z := z3, carry_out := c3 } ← Addition8FullCarry.main ⟨ x.x3, y.x3, c2 ⟩
  return { z := U32.mk z0 z1 z2 z3, carry_out := c3 }

def Assumptions (input : Inputs (F p)) :=
  let ⟨x, y, carry_in⟩ := input
  x.Normalized ∧ y.Normalized ∧ (carry_in = 0 ∨ carry_in = 1)

def Spec (input : Inputs (F p)) (out: Outputs (F p)) :=
  let ⟨x, y, carry_in⟩ := input
  let ⟨z, carry_out⟩ := out
  z.value = (x.value + y.value + carry_in.val) % 2^32
  ∧ carry_out.val = (x.value + y.value + carry_in.val) / 2^32
  ∧ z.Normalized ∧ (carry_out = 0 ∨ carry_out = 1)

/--
Elaborated circuit data can be found as follows:
```
#eval (main (p:=p_babybear) default).localLength
#eval (main (p:=p_babybear) default).output
```
-/
instance elaborated : ElaboratedCircuit (F p) Inputs Outputs where
  main := main
  localLength _ := 8
  -- unfortunately, `rfl` in default tactic times out here
  localLength_eq _ i0 := by
    simp only [circuit_norm, main, Addition8FullCarry.main, Boolean.circuit]

theorem soundness : Soundness (F p) elaborated Assumptions Spec := by
  rintro i0 env ⟨ x_var, y_var, carry_in_var ⟩ ⟨ x, y, carry_in ⟩ h_inputs as h

  let ⟨ x0, x1, x2, x3 ⟩ := x
  let ⟨ y0, y1, y2, y3 ⟩ := y
  let ⟨ x0_var, x1_var, x2_var, x3_var ⟩ := x_var
  let ⟨ y0_var, y1_var, y2_var, y3_var ⟩ := y_var
  simp only [circuit_norm, explicit_provable_type, Inputs.mk.injEq, U32.mk.injEq] at h_inputs

  -- simplify assumptions
  dsimp only [Assumptions, U32.Normalized] at as
  obtain ⟨ x_norm, y_norm, carry_in_bool ⟩ := as
  obtain ⟨ x0_byte, x1_byte, x2_byte, x3_byte ⟩ := x_norm
  obtain ⟨ y0_byte, y1_byte, y2_byte, y3_byte ⟩ := y_norm

  -- simplify circuit
  dsimp only [circuit_norm, subcircuit_norm, main, Addition8FullCarry.main, Spec, Boolean.circuit, U32.value, U32.Normalized] at h ⊢
  simp only [circuit_norm, subcircuit_norm, explicit_provable_type, h_inputs, ByteTable] at h ⊢
  set z0 := env.get i0
  set c0 := env.get (i0 + 1)
  set z1 := env.get (i0 + 2)
  set c1 := env.get (i0 + 3)
  set z2 := env.get (i0 + 4)
  set c2 := env.get (i0 + 5)
  set z3 := env.get (i0 + 6)
  set c3 := env.get (i0 + 7)
  obtain ⟨ z0_byte, c0_bool, h0, z1_byte, c1_bool, h1, z2_byte, c2_bool, h2, z3_byte, c3_bool, h3 ⟩ := h

  -- get rid of the boolean carry_out and normalized output
  simp only [c3_bool, z0_byte, z1_byte, z2_byte, z3_byte, and_self, and_true]
  rw [add_neg_eq_zero, add_neg_eq_iff_eq_add] at h0 h1 h2 h3

  -- apply the main soundness theorem
  apply Addition32.Theorems.add32_soundness
    x0_byte x1_byte x2_byte x3_byte
    y0_byte y1_byte y2_byte y3_byte
    z0_byte z1_byte z2_byte z3_byte
    carry_in_bool c0_bool c1_bool c2_bool c3_bool
    h0 h1 h2 h3


theorem completeness : Completeness (F p) elaborated Assumptions := by
  rintro i0 env ⟨ x_var, y_var, carry_in_var ⟩ henv  ⟨ x, y, carry_in ⟩ h_inputs as
  let ⟨ x0, x1, x2, x3 ⟩ := x
  let ⟨ y0, y1, y2, y3 ⟩ := y
  let ⟨ x0_var, x1_var, x2_var, x3_var ⟩ := x_var
  let ⟨ y0_var, y1_var, y2_var, y3_var ⟩ := y_var
  simp only [circuit_norm, explicit_provable_type, Inputs.mk.injEq, U32.mk.injEq] at h_inputs

  -- simplify assumptions
  dsimp [Assumptions, U32.Normalized] at as
  have ⟨ x_norm, y_norm, carry_in_bool ⟩ := as
  have ⟨ x0_byte, x1_byte, x2_byte, x3_byte ⟩ := x_norm
  have ⟨ y0_byte, y1_byte, y2_byte, y3_byte ⟩ := y_norm

  -- simplify circuit
  dsimp only [circuit_norm, subcircuit_norm, main, Addition8FullCarry.main, Boolean.circuit] at henv ⊢
  simp only [h_inputs, circuit_norm, subcircuit_norm] at henv ⊢

  -- characterize local witnesses
  obtain ⟨ hz0, hc0, hz1, hc1, hz2, hc2, hz3, hc3 ⟩ := henv

  set z0 := env.get i0
  set c0 := env.get (i0 + 1)
  set z1 := env.get (i0 + 2)
  set c1 := env.get (i0 + 3)
  set z2 := env.get (i0 + 4)
  set c2 := env.get (i0 + 5)
  set z3 := env.get (i0 + 6)
  set c3 := env.get (i0 + 7)

  -- the add8 completeness proof, four times
  have add8_completeness {x y c_in z c_out : F p}
    (hz: z = mod256 (x + y + c_in)) (hc_out: c_out = floorDiv256 (x + y + c_in)) :
    x.val < 256 → y.val < 256 → c_in = 0 ∨ c_in = 1 →
    z.val < 256 ∧ (c_out = 0 ∨ c_out = 1) ∧ x + y + c_in + -z + -(c_out * 256) = 0
  := by
    intro x_byte y_byte hc
    have : z.val < 256 := hz ▸ ByteUtils.mod256_lt (x + y + c_in)
    use this
    have carry_lt_2 : c_in.val < 2 := FieldUtils.boolean_lt_2 hc
    have : (x + y + c_in).val < 512 :=
      ByteUtils.byte_sum_and_bit_lt_512 x y c_in x_byte y_byte carry_lt_2
    use (hc_out ▸ ByteUtils.floorDiv256_bool this)
    rw [ByteUtils.mod_add_div256 (x + y + c_in), hz, hc_out]
    ring

  have ⟨ z0_byte, c0_bool, h0 ⟩ := add8_completeness hz0 hc0 x0_byte y0_byte carry_in_bool
  have ⟨ z1_byte, c1_bool, h1 ⟩ := add8_completeness hz1 hc1 x1_byte y1_byte c0_bool
  have ⟨ z2_byte, c2_bool, h2 ⟩ := add8_completeness hz2 hc2 x2_byte y2_byte c1_bool
  have ⟨ z3_byte, c3_bool, h3 ⟩ := add8_completeness hz3 hc3 x3_byte y3_byte c2_bool

  exact ⟨ z0_byte, c0_bool, h0, z1_byte, c1_bool, h1, z2_byte, c2_bool, h2, z3_byte, c3_bool, h3 ⟩

def circuit : FormalCircuit (F p) Inputs Outputs where
  Assumptions
  Spec
  soundness
  completeness
end Gadgets.Addition32Full
