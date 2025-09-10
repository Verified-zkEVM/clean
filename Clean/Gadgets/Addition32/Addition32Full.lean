import Clean.Gadgets.Addition8.Addition8FullCarry
import Clean.Types.U32
import Clean.Gadgets.Addition32.Theorems
import Clean.Utils.Primes
import Clean.Gadgets.Boolean
import Clean.Utils.Tactics

namespace Gadgets.Addition32Full
variable {p : ℕ} [Fact p.Prime] [Fact (p > 512)]

open ByteUtils (mod256 floorDiv256)

structure Inputs (F : Type) where
  x: U32 F
  y: U32 F
  carryIn: F

instance : ProvableStruct Inputs where
  components := [U32, U32, field]
  toComponents := fun {x, y, carryIn} => .cons x ( .cons y ( .cons carryIn .nil))
  fromComponents := fun (.cons x ( .cons y ( .cons carryIn .nil))) => ⟨ x, y, carryIn ⟩

structure Outputs (F : Type) where
  z: U32 F
  carryOut: F
deriving Repr

instance : ProvableStruct Outputs where
  components := [U32, field]
  toComponents := fun {z, carryOut} => .cons z ( .cons carryOut .nil)
  fromComponents := fun (.cons z ( .cons carryOut .nil)) => ⟨ z, carryOut ⟩

def main {sentences : PropertySet (F p)} (order : SentenceOrder sentences) (input : Var Inputs (F p)) : Circuit sentences (Var Outputs (F p)) := do
  let ⟨x, y, carryIn⟩ := input
  let { z := z0, carryOut := c0 } ← Addition8FullCarry.main order ⟨ x.x0, y.x0, carryIn ⟩
  let { z := z1, carryOut := c1 } ← Addition8FullCarry.main order ⟨ x.x1, y.x1, c0 ⟩
  let { z := z2, carryOut := c2 } ← Addition8FullCarry.main order ⟨ x.x2, y.x2, c1 ⟩
  let { z := z3, carryOut := c3 } ← Addition8FullCarry.main order ⟨ x.x3, y.x3, c2 ⟩
  return { z := U32.mk z0 z1 z2 z3, carryOut := c3 }

def Assumptions (input : Inputs (F p)) :=
  let ⟨x, y, carryIn⟩ := input
  x.Normalized ∧ y.Normalized ∧ IsBool carryIn

def Spec {sentences : PropertySet (F p)} (_checked : CheckedYields sentences) (input : Inputs (F p)) (out : Outputs (F p)) :=
  let ⟨x, y, carryIn⟩ := input
  let ⟨z, carryOut⟩ := out
  z.value = (x.value + y.value + carryIn.val) % 2^32
  ∧ carryOut.val = (x.value + y.value + carryIn.val) / 2^32
  ∧ z.Normalized ∧ IsBool carryOut

/--
Elaborated circuit data can be found as follows:
```
#eval (main (p:=p_babybear) default).localLength
#eval (main (p:=p_babybear) default).output
```
-/
def elaborated {sentences : PropertySet (F p)} (order : SentenceOrder sentences) : ElaboratedCircuit (F p) sentences Inputs Outputs where
  main := main order
  localLength _ := 8
  -- unfortunately, `rfl` in default tactic times out here
  localLength_eq _ i0 := by
    simp only [circuit_norm, main, Addition8FullCarry.main]

theorem soundness {sentences : PropertySet (F p)} {order : SentenceOrder sentences} : Soundness (F p) (elaborated order) order Assumptions Spec := by
  circuit_proof_start [elaborated, Addition8FullCarry.main, ByteTable, U32.value, U32.Normalized]

  constructor
  · -- Prove yielded sentences hold (vacuous - no yields)
    intro s hs _
    -- The Addition8FullCarry subcircuits don't yield anything
    sorry

  -- simplify circuit further
  -- TODO handle simplification of general provable types in `circuit_proof_start`
  let ⟨ x0, x1, x2, x3 ⟩ := input_x
  let ⟨ y0, y1, y2, y3 ⟩ := input_y
  let ⟨ x0_var, x1_var, x2_var, x3_var ⟩ := input_var_x
  let ⟨ y0_var, y1_var, y2_var, y3_var ⟩ := input_var_y
  simp only [circuit_norm, explicit_provable_type, U32.mk.injEq] at h_input
  simp only [circuit_norm, explicit_provable_type, h_input] at *

  -- introduce intermediate variables, like in the circuit
  set z0 := env.get i₀
  set c0 := env.get (i₀ + 1)
  set z1 := env.get (i₀ + 2)
  set c1 := env.get (i₀ + 3)
  set z2 := env.get (i₀ + 4)
  set c2 := env.get (i₀ + 5)
  set z3 := env.get (i₀ + 6)
  set c3 := env.get (i₀ + 7)

  -- get rid of the boolean carry_out and normalized output
  simp only [h_holds, and_self, and_true]

  -- apply the main soundness theorem
  obtain ⟨ z0_byte, c0_bool, h0, z1_byte, c1_bool, h1, z2_byte, c2_bool, h2, z3_byte, c3_bool, h3 ⟩ := h_holds
  rw [add_neg_eq_zero, add_neg_eq_iff_eq_add] at h0 h1 h2 h3

  obtain ⟨ x_norm, y_norm, carry_in_bool ⟩ := h_assumptions
  obtain ⟨ x0_byte, x1_byte, x2_byte, x3_byte ⟩ := x_norm
  obtain ⟨ y0_byte, y1_byte, y2_byte, y3_byte ⟩ := y_norm

  apply Addition32.Theorems.add32_soundness
    x0_byte x1_byte x2_byte x3_byte
    y0_byte y1_byte y2_byte y3_byte
    z0_byte z1_byte z2_byte z3_byte
    carry_in_bool c0_bool c1_bool c2_bool c3_bool
    h0 h1 h2 h3

theorem completeness {sentences : PropertySet (F p)} {order : SentenceOrder sentences} : Completeness (F p) sentences (elaborated order) Assumptions := by
  circuit_proof_start [Addition8FullCarry.main, ByteTable, U32.Normalized]

  -- simplify circuit further TODO
  let ⟨ x0, x1, x2, x3 ⟩ := input_x
  let ⟨ y0, y1, y2, y3 ⟩ := input_y
  let ⟨ x0_var, x1_var, x2_var, x3_var ⟩ := input_var_x
  let ⟨ y0_var, y1_var, y2_var, y3_var ⟩ := input_var_y
  simp only [circuit_norm, explicit_provable_type, U32.mk.injEq] at h_input
  simp only [circuit_norm, explicit_provable_type, h_input] at *

  -- introduce intermediate variables, like in the circuit
  set z0 := env.get i₀
  set c0 := env.get (i₀ + 1)
  set z1 := env.get (i₀ + 2)
  set c1 := env.get (i₀ + 3)
  set z2 := env.get (i₀ + 4)
  set c2 := env.get (i₀ + 5)
  set z3 := env.get (i₀ + 6)
  set c3 := env.get (i₀ + 7)
  obtain ⟨ hz0, hc0, hz1, hc1, hz2, hc2, hz3, hc3 ⟩ := h_env

  -- the add8 completeness proof, four times
  have add8_completeness {x y c_in z c_out : F p}
    (hz : z = mod256 (x + y + c_in)) (hc_out : c_out = floorDiv256 (x + y + c_in)) :
    x.val < 256 → y.val < 256 → IsBool c_in →
    z.val < 256 ∧ IsBool c_out ∧ x + y + c_in + -z + -(c_out * 256) = 0
  := by
    intro x_byte y_byte hc
    have : z.val < 256 := hz ▸ ByteUtils.mod256_lt (x + y + c_in)
    use this
    have carry_lt_2 : c_in.val < 2 := IsBool.val_lt_two hc
    have : (x + y + c_in).val < 512 :=
      ByteUtils.byte_sum_and_bit_lt_512 x y c_in x_byte y_byte carry_lt_2
    use (hc_out ▸ ByteUtils.floorDiv256_bool this)
    rw [ByteUtils.mod_add_div256 (x + y + c_in), hz, hc_out]
    ring

  have ⟨ x_norm, y_norm, carry_in_bool ⟩ := h_assumptions
  have ⟨ x0_byte, x1_byte, x2_byte, x3_byte ⟩ := x_norm
  have ⟨ y0_byte, y1_byte, y2_byte, y3_byte ⟩ := y_norm
  have ⟨ z0_byte, c0_bool, h0 ⟩ := add8_completeness hz0 hc0 x0_byte y0_byte carry_in_bool
  have ⟨ z1_byte, c1_bool, h1 ⟩ := add8_completeness hz1 hc1 x1_byte y1_byte c0_bool
  have ⟨ z2_byte, c2_bool, h2 ⟩ := add8_completeness hz2 hc2 x2_byte y2_byte c1_bool
  have ⟨ z3_byte, c3_bool, h3 ⟩ := add8_completeness hz3 hc3 x3_byte y3_byte c2_bool

  exact ⟨ z0_byte, c0_bool, h0, z1_byte, c1_bool, h1, z2_byte, c2_bool, h2, z3_byte, c3_bool, h3 ⟩

def circuit {sentences : PropertySet (F p)} (order : SentenceOrder sentences) : FormalCircuit order Inputs Outputs where
  elaborated := elaborated order
  Assumptions := Assumptions
  Spec := Spec
  soundness := soundness
  completeness := completeness
end Gadgets.Addition32Full
