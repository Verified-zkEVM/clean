/-
This file provides the built-in `assertEquals` gadget, which works for any provable type
and smoothly simplifies to an equality statement under `circuit_norm`.
-/
import Clean.Circuit.Loops

variable {F : Type} [Field F]
open Circuit (ConstraintsHold)

namespace Gadgets
def all_zero {n} (xs : Vector (Expression F) n) : Circuit F Unit := .forEach xs assertZero

theorem all_zero.soundness {offset : ℕ} {env : Environment F} {n} {xs : Vector (Expression F) n} :
    ConstraintsHold.Soundness env ((all_zero xs).operations offset) → ∀ x ∈ xs, x.eval env = 0 := by
  simp only [all_zero, circuit_norm]
  intro h_holds x hx
  obtain ⟨i, hi, rfl⟩ := Vector.getElem_of_mem hx
  exact h_holds ⟨i, hi⟩

theorem all_zero.completeness {offset : ℕ} {env : Environment F} {n} {xs : Vector (Expression F) n} :
    (∀ x ∈ xs, x.eval env = 0) → ConstraintsHold.Completeness env ((all_zero xs).operations offset) := by
  simp only [all_zero, circuit_norm]
  intro h_holds i
  exact h_holds xs[i] (Vector.mem_of_getElem rfl)

namespace Equality
def main {α : TypeMap} [ProvableType α] (input : Var α F × Var α F) : Circuit F Unit := do
  let (x, y) := input
  let diffs := (toVars x).zip (toVars y) |>.map (fun (xi, yi) => xi - yi)
  .forEach diffs assertZero

@[reducible]
instance elaborated (α : TypeMap) [ProvableType α] : ElaboratedCircuit F (ProvablePair α α) unit where
  main
  localLength _ := 0
  output _ _ := ()

  localLength_eq _ n := by simp only [main, circuit_norm, mul_zero]
  subcircuitsConsistent n := by simp only [main, circuit_norm]

def circuit (α : TypeMap) [ProvableType α] : FormalAssertion F (ProvablePair α α) where
  Assumptions _ := True

  Spec : α F × α F → Prop
  | (x, y) => x = y

  soundness := by
    intro offset env input_var input h_input _ h_holds
    replace h_holds := all_zero.soundness h_holds
    simp only at h_holds

    let ⟨x, y⟩ := input
    let ⟨x_var, y_var⟩ := input_var
    simp only [circuit_norm, Prod.mk.injEq] at h_input
    obtain ⟨ hx, hy ⟩ := h_input
    rw [←hx, ←hy]
    simp only [eval]
    congr 1
    ext i hi
    simp only [Vector.getElem_map]

    rw [toVars, toVars, ←Vector.forall_getElem] at h_holds
    specialize h_holds i hi
    rw [Vector.getElem_map, Vector.getElem_zip] at h_holds
    simp only [Expression.eval] at h_holds
    rw [neg_one_mul] at h_holds
    exact eq_of_add_neg_eq_zero h_holds

  completeness := by
    intro offset env input_var h_env input  h_input _ h_spec
    apply all_zero.completeness
    simp only

    let ⟨x, y⟩ := input
    let ⟨x_var, y_var⟩ := input_var
    simp only [circuit_norm, Prod.mk.injEq] at h_input
    obtain ⟨ hx, hy ⟩ := h_input
    rw [←hx, ←hy] at h_spec
    clear hx hy
    apply_fun toElements at h_spec
    simp only [eval, ProvableType.toElements_fromElements, toVars] at h_spec
    rw [Vector.ext_iff] at h_spec

    rw [toVars, toVars, ←Vector.forall_getElem]
    intro i hi
    specialize h_spec i hi
    simp only [Vector.getElem_map] at h_spec
    simp only [Vector.getElem_map, Vector.getElem_zip, Expression.eval, neg_one_mul]
    rw [h_spec]
    ring

-- allow `circuit_norm` to elaborate properties of the `circuit` while keeping main/spec/assumptions opaque
@[circuit_norm ↓]
lemma elaborated_eq (α : TypeMap) [ProvableType α] : (circuit α (F:=F)).toElaboratedCircuit = elaborated α := rfl

-- rewrite soundness/completeness directly

@[circuit_norm]
theorem soundness (α : TypeMap) [ProvableType α] (n : ℕ) (env : Environment F) (x y : Var α F) :
    ((circuit α).toSubcircuit n (x, y)).Soundness env = (eval env x = eval env y) := by
  simp only [subcircuit_norm, circuit_norm, circuit]

@[circuit_norm]
theorem completeness (α : TypeMap) [ProvableType α] (n : ℕ) (env : Environment F) (x y : Var α F) :
    ((circuit α).toSubcircuit n (x, y)).Completeness env = (eval env x = eval env y) := by
  simp only [subcircuit_norm, circuit_norm, circuit]

@[circuit_norm]
theorem usesLocalWitnesses (α : TypeMap) [ProvableType α] (n : ℕ) (env : Environment F) (x y : Var α F) :
    ((circuit α).toSubcircuit n (x, y)).UsesLocalWitnesses env = True := by
  simp only [FormalAssertion.toSubcircuit, circuit]

end Equality
end Gadgets

-- Defines a unified `===` notation for asserting equality in circuits.

@[circuit_norm]
def assertEquals {F : Type} [Field F] {α : TypeMap} [ProvableType α]
  (x y : α (Expression F)) : Circuit F Unit :=
  assertion (Gadgets.Equality.circuit α) (x, y)

@[circuit_norm, reducible]
def Expression.assertEquals {F : Type} [Field F]
  (x y : Expression F) : Circuit F Unit :=
  assertion (Gadgets.Equality.circuit id) (x, y)

class HasAssertEq (β : Type) (F : outParam Type) [Field F] where
  assert_eq : β → β → Circuit F Unit

instance {F : Type} [Field F] : HasAssertEq (Expression F) F where
  assert_eq := Expression.assertEquals

instance {F : Type} [Field F] {α : TypeMap} [ProvableType α] :
  HasAssertEq (α (Expression F)) F where
  assert_eq := @assertEquals F _ α _

attribute [circuit_norm] HasAssertEq.assert_eq
infix:50 " === " => HasAssertEq.assert_eq
