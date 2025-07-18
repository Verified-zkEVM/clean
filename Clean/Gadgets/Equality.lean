/-
This file provides the built-in `assertEquals` gadget, which works for any provable type
and smoothly simplifies to an equality statement under `circuit_norm`.
-/
import Clean.Circuit.Loops
import Clean.Circuit.Stable

variable {F : Type} [Field F]
open Circuit (ConstraintsHold)

namespace Gadgets
def allZero {n} (xs : Vector (Expression F) n) : Circuit F Unit := .forEach xs assertZero

theorem allZero.soundness {offset : ℕ} {env : Environment F} {n} {xs : Vector (Expression F) n} :
    ConstraintsHold.Soundness env ((allZero xs).operations offset) → ∀ x ∈ xs, x.eval env = 0 := by
  simp only [allZero, circuit_norm]
  intro h_holds x hx
  obtain ⟨i, hi, rfl⟩ := Vector.getElem_of_mem hx
  exact h_holds ⟨i, hi⟩

theorem allZero.completeness {offset : ℕ} {env : Environment F} {n} {xs : Vector (Expression F) n} :
    (∀ x ∈ xs, x.eval env = 0) → ConstraintsHold.Completeness env ((allZero xs).operations offset) := by
  simp only [allZero, circuit_norm]
  intro h_holds i
  exact h_holds xs[i] (Vector.mem_of_getElem rfl)

namespace Equality
def main {α : TypeMap} [ProvableType α] (input : Var α F × Var α F) : Circuit F Unit := do
  let (x, y) := input
  let diffs := (toVars x).zip (toVars y) |>.map (fun (xi, yi) => xi - yi)
  .forEach diffs assertZero

@[reducible]
instance stable_elaborated (α : TypeMap) [ProvableType α] : Circuit.StableElaboratedCircuit F (ProvablePair α α) unit where
  main
  localLength _ := 0
  output _ _ := ()

  localLength_eq _ n := by simp only [main, circuit_norm, mul_zero]
  subcircuitsConsistent n := by simp only [main, circuit_norm]

  -- Stability properties
  output_stable _ _ _ := rfl  -- output is always unit

  constraints_soundness_stable env input_var offset := by
    -- We need to show that the constraints are equivalent
    -- The key insight: the differences evaluate to the same values
    -- whether we use input_var or const (eval env input_var)
    sorry -- This requires proving that the forEach assertZero constraints are stable

  constraints_completeness_stable env input_var offset := by
    -- Same reasoning as soundness
    sorry -- This requires proving that the forEach assertZero constraints are stable

  uses_local_witnesses_stable env input_var offset := by
    -- No local witnesses, so trivially stable
    simp only [main, circuit_norm]
    -- Both sides are True since there are no witness operations
    simp only [Environment.UsesLocalWitnessesCompleteness]

-- First define the stable circuit without simps
def stable_circuit (α : TypeMap) [ProvableType α] : Circuit.StableFormalAssertion F (ProvablePair α α) where
  elaborated := stable_elaborated α
  Assumptions _ := True

  Spec : α F × α F → Prop
  | (x, y) => x = y

  soundness := by
    intro offset env input _ h_constraints
    -- Work directly with the input values
    let ⟨x, y⟩ := input
    -- The constraints check that all components are equal
    simp only [main, circuit_norm] at h_constraints
    replace h_constraints := allZero.soundness h_constraints

    -- Show that x = y by showing all components are equal
    simp only [eval, const]
    apply ProvableType.ext
    intro i hi

    rw [toVars, toVars, ←Vector.forall_getElem] at h_constraints
    specialize h_constraints i hi
    simp [Vector.getElem_map, Vector.getElem_zip, Expression.eval] at h_constraints
    rw [neg_one_mul] at h_constraints
    exact eq_of_add_neg_eq_zero h_constraints

  completeness := by
    intro offset env input h_env _ h_spec
    -- Work directly with the input values
    let ⟨x, y⟩ := input
    apply allZero.completeness

    -- h_spec tells us x = y
    rw [toVars, toVars, ←Vector.forall_getElem]
    intro i hi
    simp [Vector.getElem_map, Vector.getElem_zip, Expression.eval, const]
    rw [neg_one_mul]
    -- Since x = y, their components are equal
    have : x = y := h_spec
    rw [this]
    ring

-- For backward compatibility, define the old circuit in terms of the stable one
@[simps! (config := {isSimp := false, attrs := [`circuit_norm]})]
def circuit (α : TypeMap) [ProvableType α] : Circuit.FormalAssertion F (ProvablePair α α) :=
  (stable_circuit α).toFormalAssertion

-- For backward compatibility
@[reducible]
instance elaborated (α : TypeMap) [ProvableType α] : Circuit.ElaboratedCircuit F (ProvablePair α α) unit :=
  (stable_elaborated α).toElaboratedCircuit

-- allow `circuit_norm` to elaborate properties of the `circuit` while keeping main/spec/assumptions opaque
@[circuit_norm ↓]
lemma elaborated_eq (α : TypeMap) [ProvableType α] : (circuit α (F:=F)).elaborated = elaborated α := by
  simp [circuit, Circuit.StableFormalAssertion.toFormalAssertion, elaborated]
  rfl

-- rewrite soundness/completeness directly

@[circuit_norm]
theorem soundness (α : TypeMap) [ProvableType α] (n : ℕ) (env : Environment F) (x y : Var α F) :
    ((circuit α).toSubcircuit n (x, y)).Soundness env = (eval env x = eval env y) := by
  simp only [circuit_norm, circuit]
  -- The circuit is defined via stable_circuit, so we need to unfold through the conversion
  simp only [Circuit.StableFormalAssertion.toFormalAssertion]
  -- Now we have the soundness of the stable assertion
  simp only [Circuit.StableElaboratedCircuit.asElaboratedCircuit]
  rfl

@[circuit_norm]
theorem completeness (α : TypeMap) [ProvableType α] (n : ℕ) (env : Environment F) (x y : Var α F) :
    ((circuit α).toSubcircuit n (x, y)).Completeness env = (eval env x = eval env y) := by
  simp only [circuit_norm, circuit]
  -- The circuit is defined via stable_circuit, so we need to unfold through the conversion
  simp only [Circuit.StableFormalAssertion.toFormalAssertion]
  -- Now we have the completeness of the stable assertion
  simp only [Circuit.StableElaboratedCircuit.asElaboratedCircuit]
  rfl

@[circuit_norm]
theorem usesLocalWitnesses (α : TypeMap) [ProvableType α] (n : ℕ) (env : Environment F) (x y : Var α F) :
    ((circuit α).toSubcircuit n (x, y)).UsesLocalWitnesses env = True := by
  simp only [circuit_norm, circuit]
  -- The circuit is defined via stable_circuit, so we need to unfold through the conversion
  simp only [Circuit.StableFormalAssertion.toFormalAssertion]
  -- UsesLocalWitnesses is always True for assertions
  rfl

end Equality
end Gadgets

-- Defines a unified `===` notation for asserting equality in circuits.

@[circuit_norm]
def assertEquals {F : Type} [Field F] {α : TypeMap} [ProvableType α]
    (x y : α (Expression F)) : Circuit F Unit :=
  Gadgets.Equality.circuit α (x, y)

@[circuit_norm, reducible]
def Expression.assertEquals {F : Type} [Field F]
    (x y : Expression F) : Circuit F Unit :=
  Gadgets.Equality.circuit id (x, y)

class HasAssertEq (β : Type) (F : outParam Type) [Field F] where
  assert_eq : β → β → Circuit F Unit

instance {F : Type} [Field F] : HasAssertEq (Expression F) F where
  assert_eq := Expression.assertEquals

instance {F : Type} [Field F] {α : TypeMap} [ProvableType α] :
  HasAssertEq (α (Expression F)) F where
  assert_eq := @assertEquals F _ α _

attribute [circuit_norm] HasAssertEq.assert_eq
infix:50 " === " => HasAssertEq.assert_eq

-- Defines a unified `<==` notation for witness assignment with equality assertion in circuits.

class HasAssignEq (β : Type) (F : outParam Type) [Field F] where
  assignEq : β → Circuit F β

instance {F : Type} [Field F] : HasAssignEq (Expression F) F where
  assignEq := fun rhs => do
    let witness ← witnessField fun env => rhs.eval env
    witness === rhs
    return witness

instance {F : Type} [Field F] {α : TypeMap} [ProvableType α] :
  HasAssignEq (α (Expression F)) F where
  assignEq := fun rhs => do
    let witness ← ProvableType.witness fun env => eval env rhs
    witness === rhs
    return witness

instance {F : Type} [Field F] {n : ℕ} : HasAssignEq (Vector (Expression F) n) F :=
  inferInstanceAs (HasAssignEq (fields n (Expression F)) F)

attribute [circuit_norm] HasAssignEq.assignEq

-- Custom syntax to allow `let var <== expr` without monadic arrow
syntax "let " ident " <== " term : doElem
syntax "let " ident " : " term " <== " term : doElem

macro_rules
  | `(doElem| let $x <== $e) => `(doElem| let $x ← HasAssignEq.assignEq $e)
  | `(doElem| let $x : $t <== $e) => `(doElem| let $x : $t ← HasAssignEq.assignEq $e)
