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
  let out0 ← Addition8FullCarry.circuit ⟨input.x.x0, input.y.x0, input.carryIn⟩
  let out1 ← Addition8FullCarry.circuit ⟨input.x.x1, input.y.x1, out0.carryOut⟩
  let out2 ← Addition8FullCarry.circuit ⟨input.x.x2, input.y.x2, out1.carryOut⟩
  let out3 ← Addition8FullCarry.circuit ⟨input.x.x3, input.y.x3, out2.carryOut⟩
  return {
    z := U32.mk out0.z out1.z out2.z out3.z
    carryOut := out3.carryOut
  }

def Assumptions (input : Inputs (F p)) :=
  let ⟨x, y, carryIn⟩ := input
  x.Normalized ∧ y.Normalized ∧ IsBool carryIn

def Spec (input : Inputs (F p)) (out : Outputs (F p)) :=
  let ⟨x, y, carryIn⟩ := input
  let ⟨z, carryOut⟩ := out
  z.value = (x.value + y.value + carryIn.val) % 2^32
  ∧ carryOut.val = (x.value + y.value + carryIn.val) / 2^32
  ∧ z.Normalized ∧ IsBool carryOut

/-- Facts exposed by a byte addition's semantic specification and needed by the next limb. -/
private lemma facts_of_spec {x y carryIn z carryOut : F p}
    (x_byte : x.val < 256) (y_byte : y.val < 256) (carryIn_bool : IsBool carryIn)
    (h_spec : Addition8FullCarry.Spec { x, y, carryIn } { z, carryOut }) :
    z.val < 256 ∧ IsBool carryOut ∧ x + y + carryIn = carryOut * 256 + z := by
  rcases h_spec with ⟨h_z, h_carryOut⟩
  have carryIn_lt : carryIn.val < 2 := IsBool.val_lt_two carryIn_bool
  have sum_lt : x.val + y.val + carryIn.val < 512 := by omega
  have z_byte : z.val < 256 := by
    rw [h_z]
    exact Nat.mod_lt _ (by omega)
  have carryOut_lt : carryOut.val < 2 := by
    rw [h_carryOut]
    omega
  have carryOut_bool : IsBool carryOut := by
    rcases IsBool.nat_of_lt_two carryOut_lt with h_zero | h_one
    · left
      apply ZMod.val_injective
      simp only [h_zero, ZMod.val_zero]
    · right
      apply ZMod.val_injective
      simp only [h_one, ZMod.val_one]
  have h_add : x + y + carryIn = carryOut * 256 + z := by
    apply ZMod.val_injective
    rw [Addition32.Theorems.lift_val1 x_byte y_byte carryIn_bool,
      Addition32.Theorems.lift_val2 z_byte carryOut_bool, h_z, h_carryOut]
    have h_mod_add_div := Nat.mod_add_div (x.val + y.val + carryIn.val) 256
    omega
  exact ⟨z_byte, carryOut_bool, h_add⟩

/--
Elaborated circuit data can be found as follows:
```
#eval (main (p:=p_babybear) default).localLength
#eval (main (p:=p_babybear) default).output
```
-/
@[reducible]
instance elaborated : ElaboratedCircuit (F p) Inputs Outputs main := by
  elaborate_circuit_with {
    localLength _ := 8
    output _ i₀ := {
      z := U32.mk
        (varFromOffset field i₀)
        (varFromOffset field (i₀ + 2))
        (varFromOffset field (i₀ + 4))
        (varFromOffset field (i₀ + 6))
      carryOut := varFromOffset field (i₀ + 7)
    }
  } using by
    constructor
    · intro input
      rfl
    · constructor
      · intro input i₀
        rfl
      · simp only [circuit_norm]

theorem soundness : Soundness (F p) main Assumptions Spec := by
  circuit_proof_start [Addition8FullCarry.circuit, U32.value, U32.Normalized]

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

  obtain ⟨ x_norm, y_norm, carry_in_bool ⟩ := h_assumptions
  obtain ⟨ x0_byte, x1_byte, x2_byte, x3_byte ⟩ := x_norm
  obtain ⟨ y0_byte, y1_byte, y2_byte, y3_byte ⟩ := y_norm
  obtain ⟨ h_spec0, h_spec1, h_spec2, h_spec3 ⟩ := h_holds

  have as0 : Addition8FullCarry.Assumptions { x := x0, y := y0, carryIn := input_carryIn } :=
    ⟨x0_byte, y0_byte, carry_in_bool⟩
  obtain ⟨z0_byte, c0_bool, h0⟩ := facts_of_spec x0_byte y0_byte carry_in_bool (h_spec0 as0)
  have as1 : Addition8FullCarry.Assumptions { x := x1, y := y1, carryIn := c0 } :=
    ⟨x1_byte, y1_byte, c0_bool⟩
  obtain ⟨z1_byte, c1_bool, h1⟩ := facts_of_spec x1_byte y1_byte c0_bool (h_spec1 as1)
  have as2 : Addition8FullCarry.Assumptions { x := x2, y := y2, carryIn := c1 } :=
    ⟨x2_byte, y2_byte, c1_bool⟩
  obtain ⟨z2_byte, c2_bool, h2⟩ := facts_of_spec x2_byte y2_byte c1_bool (h_spec2 as2)
  have as3 : Addition8FullCarry.Assumptions { x := x3, y := y3, carryIn := c2 } :=
    ⟨x3_byte, y3_byte, c2_bool⟩
  obtain ⟨z3_byte, c3_bool, h3⟩ := facts_of_spec x3_byte y3_byte c2_bool (h_spec3 as3)

  have h_value := Addition32.Theorems.add32_soundness
    x0_byte x1_byte x2_byte x3_byte
    y0_byte y1_byte y2_byte y3_byte
    z0_byte z1_byte z2_byte z3_byte
    carry_in_bool c0_bool c1_bool c2_bool c3_bool
    h0 h1 h2 h3
  exact ⟨h_value.1, h_value.2, ⟨z0_byte, z1_byte, z2_byte, z3_byte⟩, c3_bool⟩

theorem completeness : Completeness (F p) main Assumptions := by
  circuit_proof_start [Addition8FullCarry.circuit, U32.Normalized]

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
  obtain ⟨h_spec0, h_spec1, h_spec2, h_spec3⟩ := h_env
  obtain ⟨x_norm, y_norm, carry_in_bool⟩ := h_assumptions
  obtain ⟨x0_byte, x1_byte, x2_byte, x3_byte⟩ := x_norm
  obtain ⟨y0_byte, y1_byte, y2_byte, y3_byte⟩ := y_norm

  have as0 : Addition8FullCarry.Assumptions { x := x0, y := y0, carryIn := input_carryIn } :=
    ⟨x0_byte, y0_byte, carry_in_bool⟩
  obtain ⟨_, c0_bool, _⟩ := facts_of_spec x0_byte y0_byte carry_in_bool (h_spec0 as0)
  have as1 : Addition8FullCarry.Assumptions { x := x1, y := y1, carryIn := c0 } :=
    ⟨x1_byte, y1_byte, c0_bool⟩
  obtain ⟨_, c1_bool, _⟩ := facts_of_spec x1_byte y1_byte c0_bool (h_spec1 as1)
  have as2 : Addition8FullCarry.Assumptions { x := x2, y := y2, carryIn := c1 } :=
    ⟨x2_byte, y2_byte, c1_bool⟩
  obtain ⟨_, c2_bool, _⟩ := facts_of_spec x2_byte y2_byte c1_bool (h_spec2 as2)
  have as3 : Addition8FullCarry.Assumptions { x := x3, y := y3, carryIn := c2 } :=
    ⟨x3_byte, y3_byte, c2_bool⟩
  exact ⟨as0, as1, as2, as3⟩

def circuit : FormalCircuit (F p) Inputs Outputs where
  main
  elaborated
  Assumptions
  Spec
  soundness
  completeness
end Gadgets.Addition32Full
