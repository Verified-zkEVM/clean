import Clean.Circuit.LookupCircuit
import Clean.Gadgets.ByteLookup
import Clean.Gadgets.Boolean
import Clean.Gadgets.Addition8.Theorems

namespace Gadgets.Addition8FullCarry
variable {p : ℕ} [Fact p.Prime] [Fact (p > 512)]

open ByteUtils (mod_256 floordiv_256)

structure Inputs (F : Type) where
  x: F
  y: F
  carry_in: F

instance : ProvableStruct Inputs where
  components := [field, field, field]
  to_components := fun { x, y, carry_in } => .cons x (.cons y (.cons carry_in .nil))
  from_components := fun (.cons x (.cons y (.cons carry_in .nil))) => { x, y, carry_in }

structure Outputs (F : Type) where
  z: F
  carry_out: F

instance : ProvableStruct Outputs where
  components := [field, field]
  to_components := fun { z, carry_out } => .cons z (.cons carry_out .nil)
  from_components := fun (.cons z (.cons carry_out .nil)) => { z, carry_out }

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
  assumptions
  spec
  local_length _ := 2
  output _ i0 := { z := var ⟨i0⟩, carry_out := var ⟨i0 + 1⟩ }

  soundness := by
    -- introductions
    rintro i0 env ⟨x_var, y_var, carry_in_var⟩ ⟨x, y, carry_in⟩ h_inputs h_assumptions h_holds

    -- characterize inputs
    replace h_inputs : x_var.eval env = x ∧ y_var.eval env = y ∧ carry_in_var.eval env = carry_in := by
      simpa [circuit_norm] using h_inputs

    -- simplify constraints, assumptions and goal
    simp_all only [circuit_norm, subcircuit_norm, h_inputs, spec, assumptions, add8_full_carry,
      ByteLookup, ByteTable, Boolean.circuit]
    set z := env.get i0
    set carry_out := env.get (i0 + 1)
    obtain ⟨ h_byte, h_bool_carry, h_add ⟩ := h_holds

    -- now it's just mathematics!
    guard_hyp h_assumptions : x.val < 256 ∧ y.val < 256 ∧ (carry_in = 0 ∨ carry_in = 1)
    guard_hyp h_byte: z.val < 256
    guard_hyp h_add: x + y + carry_in + -z + -(carry_out * 256) = 0
    guard_hyp h_bool_carry: carry_out = 0 ∨ carry_out = 1

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
    simp only [circuit_norm, subcircuit_norm, h_inputs, assumptions, add8_full_carry,
      ByteLookup, ByteTable, Boolean.circuit] at *
    obtain ⟨hz, hcarry_out⟩ := h_env
    set z := env.get i0
    set carry_out := env.get (i0 + 1)

    -- now it's just mathematics!
    guard_hyp h_assumptions : x.val < 256 ∧ y.val < 256 ∧ (carry_in = 0 ∨ carry_in = 1)

    let goal_byte := z.val < 256
    let goal_bool := carry_out = 0 ∨ carry_out = 1
    let goal_add := x + y + carry_in + -z + -(carry_out * 256) = 0
    show goal_byte ∧ goal_bool ∧ goal_add

    have completeness1 : z.val < 256 := by
      rw [hz]
      apply ByteUtils.mod_256_lt

    have ⟨as_x, as_y, as_carry_in⟩ := h_assumptions
    have carry_in_bound := FieldUtils.boolean_lt_2 as_carry_in

    have completeness2 : carry_out = 0 ∨ carry_out = 1 := by
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

  -- TODO this is not very hard, but it could be made even easier with a tactic script,
  -- or even just restructuring the statement to include the inputs hypothesis in _every_ subgoal
  computable_witnesses n input := by
    simp_all only [circuit_norm, subcircuit_norm, circuit, add8_full_carry, Boolean.circuit,
      Operations.forAllFlat, FlatOperation.forAll, Condition.applyFlat,
      Environment.only_accessed_below', Circuit.computable_witnesses', Operations.computable_witnesses,
      Inputs.mk.injEq, Array.mk.injEq, List.cons.injEq]
    intro env env' h_input env_same_below
    specialize h_input (Environment.same_below_of_le env_same_below (by linarith))
    simp_all
}

end Gadgets.Addition8FullCarry
