import Clean.Gadgets.Addition8.Addition8FullCarry
import Clean.Types.U32
import Clean.Gadgets.Addition32.Theorems
import Clean.Utils.Primes
import Clean.Gadgets.Boolean
import Clean.Utils.Tactics

namespace Gadgets.Addition32Full
variable {p : ℕ} [Fact p.Prime] [Fact (p > 512)]

open ByteUtils (mod256)
open FieldUtils (floorDiv)

structure Inputs (F : Type) where
  x: U32 F
  y: U32 F
  carryIn: F
deriving ProvableStruct

structure Outputs (F : Type) where
  z: U32 F
  carryOut: F
deriving Repr, ProvableStruct

def main (input : Var Inputs (F p)) : Circuit (F p) (Var Outputs (F p)) := do
  let ⟨x, y, carryIn⟩ := input
  let { z := z0, carryOut := c0 } ← Addition8FullCarry.main ⟨ x.x0, y.x0, carryIn ⟩
  let { z := z1, carryOut := c1 } ← Addition8FullCarry.main ⟨ x.x1, y.x1, c0 ⟩
  let { z := z2, carryOut := c2 } ← Addition8FullCarry.main ⟨ x.x2, y.x2, c1 ⟩
  let { z := z3, carryOut := c3 } ← Addition8FullCarry.main ⟨ x.x3, y.x3, c2 ⟩
  return { z := U32.mk z0 z1 z2 z3, carryOut := c3 }

def Assumptions (input : Inputs (F p)) :=
  let ⟨x, y, carryIn⟩ := input
  x.Normalized ∧ y.Normalized ∧ IsBool carryIn

def Spec (input : Inputs (F p)) (out : Outputs (F p)) :=
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
instance elaborated : ElaboratedCircuit (F p) Inputs Outputs main := by
  elaborate_circuit

theorem soundness : Soundness (F p) main Assumptions Spec := by
  circuit_proof_start [Addition8FullCarry.main, ByteTable, U32.value, U32.Normalized]

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
  rw [sub_eq_zero, sub_eq_iff_eq_add] at h0 h1 h2 h3

  obtain ⟨ x_norm, y_norm, carry_in_bool ⟩ := h_assumptions
  obtain ⟨ x0_byte, x1_byte, x2_byte, x3_byte ⟩ := x_norm
  obtain ⟨ y0_byte, y1_byte, y2_byte, y3_byte ⟩ := y_norm

  apply Addition32.Theorems.add32_soundness
    x0_byte x1_byte x2_byte x3_byte
    y0_byte y1_byte y2_byte y3_byte
    z0_byte z1_byte z2_byte z3_byte
    carry_in_bool c0_bool c1_bool c2_bool c3_bool
    h0 h1 h2 h3

theorem completeness : Completeness (F p) main Assumptions := by
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

  -- the add8 completeness proof, four times.
  -- the witness IR computes on `u64`s, but `x + y + c_in` is a sum of two bytes and a
  -- bit, hence < 512, so the `% 2 ^ 64` truncations are inert.
  have add8_completeness {x y c_in z c_out : F p}
    (x_byte : x.val < 256) (y_byte : y.val < 256) (hc : IsBool c_in)
    (hz : z = (((x + y + c_in).val % 2 ^ 64 % 256 : ℕ) : F p))
    (hc_out : c_out = (((x + y + c_in).val % 2 ^ 64 / 256 : ℕ) : F p)) :
    z.val < 256 ∧ IsBool c_out ∧ x + y + c_in - z - c_out * 256 = 0
  := by
    have carry_lt_2 : c_in.val < 2 := IsBool.val_lt_two hc
    have h512 : (x + y + c_in).val < 512 :=
      ByteUtils.byte_sum_and_bit_lt_512 x y c_in x_byte y_byte carry_lt_2
    have h_wrap : (x + y + c_in).val % 2 ^ 64 = (x + y + c_in).val :=
      Nat.mod_eq_of_lt (by omega)
    rw [h_wrap] at hz hc_out
    replace hz : z = mod256 (x + y + c_in) := hz
    replace hc_out : c_out = floorDiv (x + y + c_in) 256 := hc_out
    have : z.val < 256 := hz ▸ ByteUtils.mod256_lt (x + y + c_in)
    use this
    use (hc_out ▸ ByteUtils.floorDiv256_bool h512)
    rw [← ByteUtils.mod_add_div256 (x + y + c_in), hz, hc_out]
    ring

  have ⟨ x_norm, y_norm, carry_in_bool ⟩ := h_assumptions
  have ⟨ x0_byte, x1_byte, x2_byte, x3_byte ⟩ := x_norm
  have ⟨ y0_byte, y1_byte, y2_byte, y3_byte ⟩ := y_norm
  have ⟨ z0_byte, c0_bool, h0 ⟩ := add8_completeness x0_byte y0_byte carry_in_bool hz0 hc0
  have ⟨ z1_byte, c1_bool, h1 ⟩ := add8_completeness x1_byte y1_byte c0_bool hz1 hc1
  have ⟨ z2_byte, c2_bool, h2 ⟩ := add8_completeness x2_byte y2_byte c1_bool hz2 hc2
  have ⟨ z3_byte, c3_bool, h3 ⟩ := add8_completeness x3_byte y3_byte c2_bool hz3 hc3

  exact ⟨ z0_byte, c0_bool, h0, z1_byte, c1_bool, h1, z2_byte, c2_bool, h2, z3_byte, c3_bool, h3 ⟩

def circuit : FormalCircuit (F p) Inputs Outputs where
  main
  elaborated
  Assumptions
  Spec
  soundness
  completeness
  computableWitnesses := by
    intro n input env env'
    obtain ⟨x, y, carryIn⟩ := input
    simp only [circuit_norm, main]
    have eL : ∀ (inp : Var Addition8FullCarry.Inputs (F p)) (off : ℕ),
        Operations.localLength (Addition8FullCarry.main inp off).2 = 2 := fun _ _ => rfl
    -- the four Addition8FullCarry runs are inlined; each group's obligation comes from the
    -- child bundle's own computableWitnesses via OnlyAccessedBelow, with the carry chain's
    -- variables covered by the per-op agreement
    haveI := (Addition8FullCarry.circuit (p := p)).elaborated
    refine ⟨⟨?_, ?_, ?_, ?_⟩, fun hp hag => ?_⟩
    · apply Operations.computableWitnesses_of_premise
      intro hp
      try ring_nf
      apply (Addition8FullCarry.circuit (p := p)).computableWitnesses'_onlyAccessedBelow
      intro hag
      simp only [circuit_norm, Addition8FullCarry.main, eL] at hag ⊢
      grind
    · apply Operations.computableWitnesses_of_premise
      intro hp
      try ring_nf
      apply (Addition8FullCarry.circuit (p := p)).computableWitnesses'_onlyAccessedBelow
      intro hag
      simp only [circuit_norm, Addition8FullCarry.main, eL] at hag ⊢
      grind
    · apply Operations.computableWitnesses_of_premise
      intro hp
      try ring_nf
      apply (Addition8FullCarry.circuit (p := p)).computableWitnesses'_onlyAccessedBelow
      intro hag
      simp only [circuit_norm, Addition8FullCarry.main, eL] at hag ⊢
      grind
    · apply Operations.computableWitnesses_of_premise
      intro hp
      try ring_nf
      apply (Addition8FullCarry.circuit (p := p)).computableWitnesses'_onlyAccessedBelow
      intro hag
      simp only [circuit_norm, Addition8FullCarry.main, eL] at hag ⊢
      grind
    · -- output: the four groups' witnessed limbs and the final carry
      simp only [circuit_norm, Addition8FullCarry.main, eL] at hag ⊢
      grind
end Gadgets.Addition32Full
