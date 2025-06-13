/-
This file provides the built-in `assert_equals` gadget, which works for any provable type
and smoothly simplifies to an equality statement under `circuit_norm`.
-/
import Clean.Circuit.Loops

variable {F : Type} [Field F]
open Circuit (constraints_hold)

namespace Gadgets
def all_zero {n} (xs : Vector (Expression F) n) : Circuit F Unit := .forEach xs assert_zero

theorem all_zero.soundness {offset : ℕ} {env : Environment F} {n} {xs : Vector (Expression F) n} :
    constraints_hold.soundness env ((all_zero xs).operations offset) → ∀ x ∈ xs, x.eval env = 0 := by
  simp only [all_zero, circuit_norm]
  intro h_holds x hx
  obtain ⟨i, hi, rfl⟩ := Vector.getElem_of_mem hx
  exact h_holds ⟨i, hi⟩

theorem all_zero.completeness {offset : ℕ} {env : Environment F} {n} {xs : Vector (Expression F) n} :
    (∀ x ∈ xs, x.eval env = 0) → constraints_hold.completeness env ((all_zero xs).operations offset) := by
  simp only [all_zero, circuit_norm]
  intro h_holds i
  exact h_holds xs[i] (Vector.mem_of_getElem rfl)

namespace Equality
def main {α : TypeMap} [ProvableType α] (input : Var α F × Var α F) : Circuit F Unit := do
  let (x, y) := input
  let diffs := (to_vars x).zip (to_vars y) |>.map (fun (xi, yi) => xi - yi)
  .forEach diffs assert_zero

@[reducible]
instance elaborated (α : TypeMap) [ProvableType α] : ElaboratedCircuit F (ProvablePair α α) unit where
  main
  local_length _ := 0
  output _ _ := ()

  local_length_eq _ n := by simp only [main, circuit_norm, mul_zero]
  subcircuits_consistent n := by simp only [main, circuit_norm]

def circuit (α : TypeMap) [ProvableType α] : FormalAssertion F (ProvablePair α α) where
  assumptions _ := True

  spec : α F × α F → Prop
  | (x, y) => x = y

  soundness := by
    intro offset env input_var input h_input _ h_holds
    replace h_holds := all_zero.soundness h_holds
    simp only at h_holds

    let ⟨x, y⟩ := input
    let ⟨x_var, y_var⟩ := input_var
    simp only [circuit_norm, eval, Prod.mk.injEq] at h_input
    obtain ⟨ hx, hy ⟩ := h_input
    rw [←hx, ←hy]
    congr 1
    ext i hi
    simp only [Vector.getElem_map]

    rw [to_vars, to_vars, ←Vector.forall_getElem] at h_holds
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
    simp only [circuit_norm, eval, Prod.mk.injEq] at h_input
    obtain ⟨ hx, hy ⟩ := h_input
    rw [←hx, ←hy] at h_spec
    clear hx hy
    apply_fun to_elements at h_spec
    simp only [ProvableType.to_elements_from_elements] at h_spec
    rw [Vector.ext_iff] at h_spec

    rw [to_vars, to_vars, ←Vector.forall_getElem]
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
    ((circuit α).to_subcircuit n (x, y)).soundness env = (eval env x = eval env y) := by
  simp only [subcircuit_norm, circuit_norm, circuit]

@[circuit_norm]
theorem completeness (α : TypeMap) [ProvableType α] (n : ℕ) (env : Environment F) (x y : Var α F) :
    ((circuit α).to_subcircuit n (x, y)).completeness env = (eval env x = eval env y) := by
  simp only [subcircuit_norm, circuit_norm, circuit]

end Equality
end Gadgets

/-
Provides a unified `===` notation for asserting equality in circuits:
- Core `assert_equals` for `α (Expression F)` and `Expression F`.
- `HasAssertEq` / `HasAssertEqM` dispatch so `assert_equals_generic x y`
  and `x === y` pick the right gadget and lift via `MonadLift`.
- Marked `@[circuit_norm]`/`@[reducible]` so `dsimp only [circuit_norm]`
  unfolds `===` to the original `assert_equals`.
-/
@[circuit_norm]
def assert_equals {F : Type} [Field F] {α : TypeMap} [ProvableType α]
  (x y : α (Expression F)) : Circuit F Unit :=
  assertion (Gadgets.Equality.circuit α) (x, y)

@[circuit_norm, reducible]
def Expression.assert_equals {F : Type} [Field F]
  (x y : Expression F) : Circuit F Unit :=
  assertion (Gadgets.Equality.circuit id) (x, y)

class HasAssertEq (β : Type) (F : outParam Type) [Field F] where
  assert_eq : β → β → Circuit F Unit

@[circuit_norm, reducible]
instance {F : Type} [Field F] : HasAssertEq (Expression F) F where
  assert_eq := Expression.assert_equals

@[circuit_norm, reducible]
instance {F : Type} [Field F] {α : TypeMap} [ProvableType α] :
  HasAssertEq (α (Expression F)) F where
  assert_eq := @assert_equals F _ α _

@[circuit_norm, reducible]
def assert_equals_generic {β : Type} {F : Type} [Field F] [HasAssertEq β F]
  (x y : β) : Circuit F Unit :=
  HasAssertEq.assert_eq x y

class HasAssertEqM (β : Type) (m : Type → Type) (F : outParam Type) [Field F] where
  assert_eqM : β → β → m Unit

@[circuit_norm, reducible]
instance hasAssertEqM_Circuit {β : Type} {F : Type} [Field F] [HasAssertEq β F] :
  HasAssertEqM β (Circuit F) F where
  assert_eqM x y := assert_equals_generic x y

@[circuit_norm, reducible]
instance hasAssertEqM_lift {β : Type} {F : Type} [Field F] [HasAssertEq β F]
  {m : Type → Type} [MonadLift (Circuit F) m] :
  HasAssertEqM β m F where
  assert_eqM x y := MonadLift.monadLift (assert_equals_generic x y)

@[circuit_norm, reducible, simp]
def assert_eqM' {β : Type} {m : Type → Type} {F : Type} [Field F] [HasAssertEqM β m F]
  (x y : β) : m Unit :=
  HasAssertEqM.assert_eqM x y

infix:50 " === " => assert_eqM'

@[circuit_norm]
lemma HasAssertEq.assert_eq_eq {β : Type} {F : Type} [Field F] [inst : HasAssertEq β F]
  (x y : β) :
  inst.assert_eq x y = assert_equals_generic x y := rfl
