import Clean.Circuit.LookupCircuit
import Clean.Gadgets.ByteLookup
import Clean.Gadgets.Boolean
import Clean.Gadgets.Addition8.Theorems
import Clean.Gadgets.Boolean

open Clean

namespace Gadgets.Addition8FullCarry
variable {p : ℕ} [Fact p.Prime] [Fact (p > 512)]

open ByteUtils (mod256 floorDiv256)

structure Inputs (F : Type) where
  x: F
  y: F
  carryIn: F

instance : ProvableStruct Inputs where
  components := [field, field, field]
  toComponents := fun { x, y, carryIn } => .cons x (.cons y (.cons carryIn .nil))
  fromComponents := fun (.cons x (.cons y (.cons carryIn .nil))) => { x, y, carryIn }

structure Outputs (F : Type) where
  z: F
  carryOut: F

instance : ProvableStruct Outputs where
  components := [field, field]
  toComponents := fun { z, carryOut } => .cons z (.cons carryOut .nil)
  fromComponents := fun (.cons z (.cons carryOut .nil)) => { z, carryOut }

def main (input : Var Inputs (F p)) : Circuit (F p) (Var Outputs (F p)) := do
  let ⟨x, y, carryIn⟩ := input

  -- witness the result
  let z ← witness fun eval => mod256 (eval (x + y + carryIn))
  lookup ByteTable z

  -- witness the output carry
  let carryOut ← witness fun eval => floorDiv256 (eval (x + y + carryIn))
  assertBool carryOut

  assertZero (x + y + carryIn - z - carryOut * 256)

  return { z, carryOut }

def Assumptions (input : Inputs (F p)) :=
  let ⟨x, y, carryIn⟩ := input
  x.val < 256 ∧ y.val < 256 ∧ IsBinary carryIn

def Spec (input : Inputs (F p)) (out : Outputs (F p)) :=
  let ⟨x, y, carryIn⟩ := input
  out.z.val = (x.val + y.val + carryIn.val) % 256 ∧
  out.carryOut.val = (x.val + y.val + carryIn.val) / 256

/--
  Compute the 8-bit addition of two numbers with a carry-in bit.
  Returns the sum and the output carry bit.
-/
def circuit : FormalCircuit (F p) Inputs Outputs where
  main
  Assumptions
  Spec
  localLength _ := 2
  output _ i0 := { z := var ⟨i0⟩, carryOut := var ⟨i0 + 1⟩ }

  soundness := by
    -- introductions
    rintro i0 env ⟨x_var, y_var, carry_in_var⟩ ⟨x, y, carry_in⟩ h_inputs h_assumptions h_holds

    -- characterize inputs
    replace h_inputs : x_var.eval env = x ∧ y_var.eval env = y ∧ carry_in_var.eval env = carry_in := by
      simpa [circuit_norm] using h_inputs

    -- simplify constraints, assumptions and goal
    simp_all only [circuit_norm, subcircuit_norm, h_inputs, Spec, Assumptions, main,
      ByteTable]
    set z := env.get i0
    set carry_out := env.get (i0 + 1)
    obtain ⟨ h_byte, h_bool_carry, h_add ⟩ := h_holds

    -- now it's just mathematics!
    guard_hyp h_assumptions : x.val < 256 ∧ y.val < 256 ∧ IsBinary carry_in
    guard_hyp h_byte: z.val < 256
    guard_hyp h_add: x + y + carry_in + -z + -(carry_out * 256) = 0
    show z.val = (x.val + y.val + carry_in.val) % 256 ∧
         carry_out.val = (x.val + y.val + carry_in.val) / 256

    have ⟨as_x, as_y, as_carry_in⟩ := h_assumptions
    apply Addition8.Theorems.soundness x y z carry_in carry_out as_x as_y h_byte as_carry_in h_bool_carry h_add

  completeness := by
   -- introductions
    rintro i0 env ⟨x_var, y_var, carry_in_var⟩ h_env ⟨x, y, carry_in⟩ h_inputs h_assumptions

    -- characterize inputs
    replace h_inputs : x_var.eval env = x ∧ y_var.eval env = y ∧ carry_in_var.eval env = carry_in := by
      simpa [circuit_norm] using h_inputs

    -- simplify assumptions and goal
    simp only [circuit_norm, subcircuit_norm, h_inputs, Assumptions, main,
      ByteTable] at *
    obtain ⟨hz, hcarry_out⟩ := h_env
    set z := env.get i0
    set carry_out := env.get (i0 + 1)

    -- now it's just mathematics!
    guard_hyp h_assumptions : x.val < 256 ∧ y.val < 256 ∧ IsBinary carry_in

    let goal_byte := z.val < 256
    let goal_bool := IsBinary carry_out
    let goal_add := x + y + carry_in + -z + -(carry_out * 256) = 0
    show goal_byte ∧ goal_bool ∧ goal_add

    have completeness1 : z.val < 256 := by
      rw [hz]
      apply ByteUtils.mod256_lt

    have ⟨as_x, as_y, as_carry_in⟩ := h_assumptions
    have carry_in_bound := IsBinary.val_lt_two as_carry_in

    have completeness2 : IsBinary carry_out := by
      rw [hcarry_out]
      apply Addition8.Theorems.completeness_bool
      repeat assumption

    have completeness3 : x + y + carry_in + -z + -(carry_out * 256) = 0 := by
      rw [hz, hcarry_out]
      apply Addition8.Theorems.completeness_add
      repeat assumption

    exact ⟨completeness1, completeness2, completeness3⟩

def lookupCircuit : LookupCircuit (F p) Inputs Outputs := {
  circuit with
  name := "Addition8FullCarry"

  computableWitnesses n input := by
    simp_all only [circuit_norm, subcircuit_norm, circuit, main,
      Operations.forAllFlat, Operations.toFlat, FlatOperation.forAll, Inputs.mk.injEq]
}

end Gadgets.Addition8FullCarry
