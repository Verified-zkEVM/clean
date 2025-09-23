import Clean.Circuit.LookupCircuit
import Clean.Gadgets.ByteLookup
import Clean.Gadgets.Boolean
import Clean.Gadgets.Addition8.Theorems

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

def main {sentences : PropertySet (F p)} (order : SentenceOrder sentences)
    (input : Var Inputs (F p)) : Circuit sentences (Var Outputs (F p)) := do
  let ⟨x, y, carryIn⟩ := input

  -- witness the result
  let z ← witness fun eval => mod256 (eval (x + y + carryIn))
  lookup ByteTable z

  -- witness the output carry
  let carryOut ← witness fun eval => floorDiv256 (eval (x + y + carryIn))
  -- assert that carryOut is boolean (as a subcircuit assertion)
  assertBool order carryOut

  assertZero sentences (x + y + carryIn - z - carryOut * 256)

  return { z, carryOut }

def Assumptions (input : Inputs (F p)) :=
  let ⟨x, y, carryIn⟩ := input
  x.val < 256 ∧ y.val < 256 ∧ IsBool carryIn

def CompletenessAssumptions {sentences : PropertySet (F p)} (_ : YieldContext sentences) (input : Inputs (F p)) :=
  Assumptions input

def Spec (input : Inputs (F p)) (out : Outputs (F p)) :=
  let ⟨x, y, carryIn⟩ := input
  out.z.val = (x.val + y.val + carryIn.val) % 256 ∧
  out.carryOut.val = (x.val + y.val + carryIn.val) / 256

/--
  Compute the 8-bit addition of two numbers with a carry-in bit.
  Returns the sum and the output carry bit.
-/
def circuit {sentences : PropertySet (F p)} (order : SentenceOrder sentences)
    : FormalCircuit order Inputs Outputs where
  main := main order
  Assumptions := Assumptions
  CompletenessAssumptions := CompletenessAssumptions
  Spec _ := Spec
  localLength _ := 2
  output _ i0 := { z := var ⟨i0⟩, carryOut := var ⟨i0 + 1⟩ }
  yields _ _ _ := ∅
  yields_eq := by
    intros env input offset
    simp only [circuit_norm, main, FormalAssertion.toSubcircuit]
  completenessAssumptions_implies_assumptions := fun _ _ h => h

  soundness := by
    -- introductions
    rintro i0 env yields checked ⟨x_var, y_var, carry_in_var⟩ ⟨x, y, carry_in⟩ h_inputs h_assumptions h_holds

    -- characterize inputs
    replace h_inputs : x_var.eval env = x ∧ y_var.eval env = y ∧ carry_in_var.eval env = carry_in := by
      simpa [circuit_norm] using h_inputs

    -- simplify constraints, assumptions and goal
    simp_all only [circuit_norm, Spec, Assumptions, main, ByteTable, FormalAssertion.toSubcircuit]

    set z := env.get i0
    set carry_out := env.get (i0 + 1)
    obtain ⟨ h_byte, h_bool_carry, h_add ⟩ := h_holds

    -- now it's just mathematics!
    guard_hyp h_assumptions : x.val < 256 ∧ y.val < 256 ∧ IsBool carry_in
    guard_hyp h_byte: z.val < 256
    guard_hyp h_add: x + y + carry_in + -z + -(carry_out * 256) = 0

    show z.val = (x.val + y.val + carry_in.val) % 256 ∧
          carry_out.val = (x.val + y.val + carry_in.val) / 256
    have ⟨as_x, as_y, as_carry_in⟩ := h_assumptions
    apply Addition8.Theorems.soundness x y z carry_in carry_out as_x as_y h_byte as_carry_in h_bool_carry h_add

  completeness := by
   -- introductions
    rintro i0 env yields ⟨x_var, y_var, carry_in_var⟩ h_env ⟨x, y, carry_in⟩ h_inputs h_assumptions

    -- characterize inputs
    replace h_inputs : x_var.eval env = x ∧ y_var.eval env = y ∧ carry_in_var.eval env = carry_in := by
      simpa [circuit_norm] using h_inputs

    -- simplify assumptions and goal
    simp only [circuit_norm, h_inputs, main, ByteTable, FormalAssertion.toSubcircuit] at *
    simp only [CompletenessAssumptions, Assumptions] at h_assumptions

    obtain ⟨hz, hcarry_out⟩ := h_env
    set z := env.get i0
    set carry_out := env.get (i0 + 1)

    -- now it's just mathematics!
    guard_hyp h_assumptions : x.val < 256 ∧ y.val < 256 ∧ IsBool carry_in

    let goal_byte := z.val < 256
    let goal_bool := IsBool carry_out
    let goal_add := x + y + carry_in + -z + -(carry_out * 256) = 0
    show goal_byte ∧ goal_bool ∧ goal_add

    have completeness1 : z.val < 256 := by
      rw [hz]
      apply ByteUtils.mod256_lt

    have ⟨as_x, as_y, as_carry_in⟩ := h_assumptions
    have carry_in_bound := IsBool.val_lt_two as_carry_in

    have completeness2 : IsBool carry_out := by
      rw [hcarry_out]
      apply Addition8.Theorems.completeness_bool
      repeat assumption

    have completeness3 : x + y + carry_in + -z + -(carry_out * 256) = 0 := by
      rw [hz, hcarry_out]
      apply Addition8.Theorems.completeness_add
      repeat assumption

    exact ⟨completeness1, completeness2, completeness3⟩

def lookupCircuit : LookupCircuit (F p) Inputs Outputs := {
  circuit := circuit (emptyOrder (F p)),
  name := "Addition8FullCarry"

  computableWitnesses n input := by
    simp_all only [circuit_norm, circuit, main, FormalAssertion.toSubcircuit,
      Operations.forAllFlat, Operations.toFlat, FlatOperation.forAll, Inputs.mk.injEq]
}

end Gadgets.Addition8FullCarry
