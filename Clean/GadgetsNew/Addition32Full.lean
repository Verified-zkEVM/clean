import Mathlib.Algebra.Field.Basic
import Mathlib.Data.ZMod.Basic
import Clean.Utils.Primes
import Clean.Utils.Vector
import Clean.Circuit.Expression
import Clean.Circuit.Provable
import Clean.Circuit.Basic
import Clean.Circuit.SubCircuit
import Clean.Utils.Field
import Clean.GadgetsNew.ByteLookup
import Clean.GadgetsNew.Boolean
import Clean.GadgetsNew.Add8.Addition8FullCarry
import Clean.Types.U32

namespace Addition32Full
variable {p : ℕ} [Fact (p ≠ 0)] [Fact p.Prime]
variable [p_large_enough: Fact (p > 512)]

open Provable (field field2 fields)
open ByteLookup

structure InputStruct (F : Type) where
  x: U32 F
  y: U32 F
  carry_in: F

def Inputs (p : ℕ) : TypePair := ⟨
  InputStruct (Expression (F p)),
  InputStruct (F p)
⟩

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
    sorry

  completeness := by
    sorry
end Addition32Full
