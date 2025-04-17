import Clean.Circuit.SubCircuit
import Clean.Gadgets.ByteLookup
import Clean.Gadgets.Boolean
import Clean.Gadgets.Addition8.Theorems

namespace Gadgets.Addition8FullCarry
variable {p : ℕ} [Fact p.Prime]
variable [p_large_enough: Fact (p > 512)]

open ByteUtils (mod_256 floordiv_256)

structure Inputs (F : Type) where
  x: F
  y: F
  carry_in: F

instance : ProvableType Inputs where
  size := 3
  to_elements x := #v[x.x, x.y, x.carry_in]
  from_elements v :=
    let ⟨ .mk [x, y, carry_in], _ ⟩ := v
    ⟨ x, y, carry_in ⟩

structure Outputs (F : Type) where
  z: F
  carry_out: F

instance : ProvableType Outputs where
  size := 2
  to_elements x := #v[x.z, x.carry_out]
  from_elements v :=
    let ⟨ .mk [z, carry_out], _ ⟩ := v
    ⟨ z, carry_out ⟩

def add8_full_carry (input : Var Inputs (F p)) : Circuit (F p) (Var Outputs (F p)) := do
  let ⟨x, y, carry_in⟩ := input

  -- witness the result
  let z ← witness (fun eval => mod_256 (eval (x + y + carry_in)))
  lookup (ByteLookup z)

  -- witness the output carry
  let carry_out ← witness (fun eval => floordiv_256 (eval (x + y + carry_in)))
  assertion Boolean.circuit carry_out

  assert_zero (x + y + carry_in - z - carry_out * 256)

  return { z, carry_out }

def assumptions (input : Inputs (F p)) :=
  let ⟨x, y, carry_in⟩ := input
  x.val < 256 ∧ y.val < 256 ∧ (carry_in = 0 ∨ carry_in = 1)

def spec (input : Inputs (F p)) (out : Outputs (F p)) :=
  let ⟨x, y, carry_in⟩ := input
  out.z.val = (x.val + y.val + carry_in.val) % 256 ∧
  out.carry_out.val = (x.val + y.val + carry_in.val) / 256

/--
  Compute the 8-bit addition of two numbers with a carry-in bit.
  Returns the sum and the output carry bit.
-/
def circuit : FormalCircuit (F p) Inputs Outputs where
  main := add8_full_carry
  assumptions := assumptions
  spec := spec
  local_length _ := 2
  output _ i0 := { z := var ⟨i0⟩, carry_out := var ⟨i0 + 1⟩ }

  soundness := by
    -- introductions
    rintro i0 env inputs_var inputs h_inputs as
    let ⟨x, y, carry_in⟩ := inputs
    let ⟨x_var, y_var, carry_in_var⟩ := inputs_var
    rintro h_holds outputs
    -- characterize inputs
    have hx : x_var.eval env = x := by injection h_inputs
    have hy : y_var.eval env = y := by injection h_inputs
    have hcarry_in : carry_in_var.eval env = carry_in := by injection h_inputs

    -- simplify constraints hypothesis
    simp only [circuit_norm, add8_full_carry, ByteLookup] at h_holds
    set z := env.get i0
    set carry_out := env.get (i0 + 1)
    rw [hx, hy, hcarry_in] at h_holds
    obtain ⟨ ⟨ ⟨ _, h_byte⟩, h_bool_carry⟩, h_add ⟩ := h_holds

    rw [(by rfl : outputs = ⟨z, carry_out⟩)]

    -- simplify assumptions and spec
    dsimp [spec]
    dsimp [assumptions] at as

    -- now it's just mathematics!
    guard_hyp as : x.val < 256 ∧ y.val < 256 ∧ (carry_in = 0 ∨ carry_in = 1)
    guard_hyp h_byte: ByteTable.contains (#v[z])
    guard_hyp h_add: x + y + carry_in + -z + -(carry_out * 256) = 0
    change True → (carry_out = 0 ∨ carry_out = 1) at h_bool_carry
    specialize h_bool_carry trivial

    show z.val = (x.val + y.val + carry_in.val) % 256 ∧
         carry_out.val = (x.val + y.val + carry_in.val) / 256

    -- reuse ByteTable.soundness
    have h_byte': z.val < 256 := ByteTable.soundness z h_byte

    have ⟨as_x, as_y, as_carry_in⟩ := as
    apply Gadgets.Addition8.Theorems.soundness x y z carry_in carry_out as_x as_y h_byte' as_carry_in h_bool_carry h_add

  completeness := by
   -- introductions
    rintro i0 env inputs_var henv inputs h_inputs
    let ⟨x, y, carry_in⟩ := inputs
    let ⟨x_var, y_var, carry_in_var⟩ := inputs_var
    rintro as

    -- characterize inputs
    have hx : x_var.eval env = x := by injection h_inputs
    have hy : y_var.eval env = y := by injection h_inputs
    have hcarry_in : carry_in_var.eval env = carry_in := by injection h_inputs

    -- simplify assumptions
    dsimp [assumptions] at as

    -- unfold goal, (re)introduce names for some of unfolded variables
    simp only [add8_full_carry, circuit_norm]
    rw [hx, hy, hcarry_in]
    set z := env.get i0
    set carry_out := env.get (i0 + 1)

    -- simplify local witnesses
    have hz : z = mod_256 (x + y + carry_in) := by
      have henv0 := henv (0 : Fin 2)
      dsimp only [add8_full_carry, circuit_norm] at henv0
      rwa [hx, hy, hcarry_in] at henv0

    have hcarry_out : carry_out = floordiv_256 (x + y + carry_in) := by
      have henv1 := henv (1 : Fin 2)
      dsimp only [add8_full_carry, circuit_norm] at henv1
      rwa [hx, hy, hcarry_in] at henv1

    -- now it's just mathematics!
    guard_hyp as : x.val < 256 ∧ y.val < 256 ∧ (carry_in = 0 ∨ carry_in = 1)

    let goal_byte := ByteTable.contains (#v[z])
    let goal_bool := carry_out = 0 ∨ carry_out = 1
    let goal_add := x + y + carry_in + -z + -(carry_out * 256) = 0
    show ((True ∧ goal_byte) ∧ True ∧ goal_bool) ∧ goal_add
    suffices goal_byte ∧ goal_bool ∧ goal_add by tauto

    have completeness1 : goal_byte := ByteTable.completeness z (hz ▸ ByteUtils.mod_256_lt _)

    have ⟨as_x, as_y, as_carry_in⟩ := as
    have carry_in_bound := FieldUtils.boolean_lt_2 as_carry_in

    have completeness2 : carry_out = 0 ∨ carry_out = 1 := by
      rw [hcarry_out]
      apply Gadgets.Addition8.Theorems.completeness_bool
      repeat assumption

    have completeness3 : x + y + carry_in + -z + -(carry_out * 256) = 0 := by
      rw [hz, hcarry_out]
      apply Gadgets.Addition8.Theorems.completeness_add
      repeat assumption

    exact ⟨completeness1, completeness2, completeness3⟩

end Gadgets.Addition8FullCarry
