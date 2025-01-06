import Mathlib.Algebra.Field.Basic
import Mathlib.Data.ZMod.Basic
import Clean.Utils.Primes
import Clean.Utils.Vector
import Clean.Circuit.Expression
import Clean.Circuit.Provable
import Clean.Circuit.Basic
import Clean.Utils.Field
import Clean.GadgetsNew.ByteLookup
import Clean.GadgetsNew.Boolean
import Clean.GadgetsNew.Add8.Theorems

namespace Add8FullCarry
variable {p : ℕ} [p_neq_zero: Fact (p ≠ 0)] [Fact p.Prime]
variable [p_large_enough: Fact (p > 512)]

open Circuit
open Provable (field field2 fields)
open ByteLookup
open Expression

structure InputStruct (F : Type) where
  x: F
  y: F
  carry_in: F

def Inputs (p : ℕ) : TypePair := ⟨
  InputStruct (Expression (F p)),
  InputStruct (F p)
⟩

instance : ProvableType (F p) (Inputs p) where
  size := 3
  to_vars s := vec [s.x, s.y, s.carry_in]
  from_vars v :=
    let ⟨ [x, y, carry_in], _ ⟩ := v
    ⟨ x, y, carry_in ⟩
  to_values s := vec [s.x, s.y, s.carry_in]
  from_values v :=
    let ⟨ [x, y, carry_in], _ ⟩ := v
    ⟨ x, y, carry_in ⟩


structure OutputStruct (F : Type) where
  z: F
  carry_out: F

def Outputs (p : ℕ) : TypePair := ⟨
  OutputStruct (Expression (F p)),
  OutputStruct (F p)
⟩

instance : ProvableType (F p) (Outputs p) where
  size := 2
  to_vars s := vec [s.z, s.carry_out]
  from_vars v :=
    let ⟨ [z, carry_out], _ ⟩ := v
    ⟨ z, carry_out ⟩
  to_values s := vec [s.z, s.carry_out]
  from_values v :=
    let ⟨ [z, carry_out], _ ⟩ := v
    ⟨ z, carry_out ⟩

def add8_full_carry (input : (Inputs p).var) : Stateful (F p) (Outputs p).var := do
  let ⟨x, y, carry_in⟩ := input

  -- witness the result
  let z ← witness (fun () => FieldUtils.mod_256 (x + y + carry_in))
  byte_lookup z

  -- witness the output carry
  let carry_out ← witness (fun () => FieldUtils.floordiv (x + y + carry_in) 256)
  assert_bool carry_out

  assert_zero (x + y + carry_in - z - carry_out * (const ↑(256 : ℕ)))

  return {
    z := z,
    carry_out := carry_out
  }

def assumptions (input : (Inputs p).value) :=
  let ⟨x, y, carry_in⟩ := input
  x.val < 256 ∧ y.val < 256 ∧ (carry_in = 0 ∨ carry_in = 1)

def spec (input : (Inputs p).value) (out : (Outputs p).value) :=
  let ⟨x, y, carry_in⟩ := input
  out.z.val = (x.val + y.val + carry_in.val) % 256 ∧
  out.carry_out.val = (x.val + y.val + carry_in.val) / 256

/--
  Compute the 8-bit addition of two numbers with a carry-in bit.
  Returns the sum and the output carry bit.
-/
def circuit : FormalCircuit (F p) (Inputs p) (Outputs p) where
  main := add8_full_carry
  assumptions := assumptions
  spec := spec
  soundness := by
    -- introductions
    rintro ctx env inputs inputs_var h_inputs as
    let ⟨x, y, carry_in⟩ := inputs
    let ⟨x_var, y_var, carry_in_var⟩ := inputs_var
    rintro h_holds outputs
    -- characterize inputs
    have hx : x_var.eval_env env = x := by injection h_inputs
    have hy : y_var.eval_env env = y := by injection h_inputs
    have hcarry_in : carry_in_var.eval_env env = carry_in := by injection h_inputs

    let i0 := ctx.offset
    let i1 := ctx.offset + 1
    -- simplify constraints hypothesis
    dsimp at h_holds
    let z := env i0
    set carry_out := env i1
    rw [←(by rfl : z = env i0)] at h_holds
    rw [hx, hy, hcarry_in] at h_holds
    let ⟨ h_byte, h_bool_carry, h_add ⟩ := h_holds

    rw [(by rfl : outputs = ⟨z, carry_out⟩)]

    -- simplify assumptions and spec
    dsimp [spec]
    dsimp [assumptions] at as

    -- now it's just mathematics!
    guard_hyp as : x.val < 256 ∧ y.val < 256 ∧ (carry_in = 0 ∨ carry_in = 1)
    guard_hyp h_byte: ByteTable.contains (vec [z])
    guard_hyp h_bool_carry: carry_out * (carry_out + -1 * 1) = 0
    guard_hyp h_add: x + y + carry_in + -1 * z + -1 * (carry_out * 256) = 0

    show z.val = (x.val + y.val + carry_in.val) % 256 ∧
         carry_out.val = (x.val + y.val + carry_in.val) / 256

    -- reuse Boolean.equiv
    have h_bool_carry': carry_out = 0 ∨ carry_out = 1 := (Boolean.equiv carry_out).mp h_bool_carry
    -- reuse ByteTable.soundness
    have h_byte': z.val < 256 := ByteTable.soundness z h_byte

    have ⟨as_x, as_y, as_carry_in⟩ := as
    apply Add8Theorems.soundness x y z carry_in carry_out as_x as_y h_byte' as_carry_in h_bool_carry' h_add

  completeness := by
   -- introductions
    rintro ctx inputs inputs_var h_inputs
    let ⟨x, y, carry_in⟩ := inputs
    let ⟨x_var, y_var, carry_in_var⟩ := inputs_var
    rintro as

    -- characterize inputs
    have hx : x_var.eval = x := by injection h_inputs
    have hy : y_var.eval = y := by injection h_inputs
    have hcarry_in : carry_in_var.eval = carry_in := by injection h_inputs

    -- simplify assumptions
    dsimp [assumptions] at as

    -- unfold goal, (re)introduce names for some of unfolded variables
    dsimp
    rw [hx, hy, hcarry_in]
    let z := FieldUtils.mod_256 (x + y + carry_in)
    let carry_out := FieldUtils.floordiv (x + y + carry_in) 256
    rw [←(by rfl : z = FieldUtils.mod_256 (x + y + carry_in))]
    rw [←(by rfl : carry_out = FieldUtils.floordiv (x + y + carry_in) 256)]

    -- now it's just mathematics!
    guard_hyp as : x.val < 256 ∧ y.val < 256 ∧ (carry_in = 0 ∨ carry_in = 1)

    let goal_byte := ByteTable.contains (vec [z])
    let goal_bool := carry_out * (carry_out + -1 * 1) = 0
    let goal_add := x + y + carry_in + -1 * z + -1 * (carry_out * 256) = 0
    show goal_byte ∧ goal_bool ∧ goal_add

    -- proving that z is contained in the Byte table is simple,
    -- so we just do it inline applying the fact that every byte is contained in
    -- the Byte table
    have completeness1 : goal_byte := ByteTable.completeness z (by
      dsimp [z]
      simp only [FieldUtils.mod_256, FieldUtils.mod]
      rw [FieldUtils.val_of_nat_to_field_eq]
      apply Nat.mod_lt
      linarith)

    have ⟨as_x, as_y, as_carry_in⟩ := as
    have carry_in_bound := FieldUtils.boolean_le_2 carry_in as_carry_in

    have completeness2 : goal_bool := by
      apply Add8Theorems.completeness_bool
      repeat assumption

    have completeness3 : goal_add := by
      apply Add8Theorems.completeness_add
      repeat assumption

    exact ⟨completeness1, completeness2, completeness3⟩

end Add8FullCarry
