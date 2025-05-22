/-
This file provides the built-in `assert_equals` gadget, which works for any provable type
and smoothly simplifies to an equality statement under `circuit_norm`.
-/
import Clean.Circuit.Loops

variable {F : Type} [Field F]
open Circuit (constraints_hold)

namespace Gadgets
def all_zero {n} (xs : Vector (Expression F) n) : Circuit F Unit := forM xs assert_zero

theorem all_zero.soundness {offset : ℕ} {env : Environment F} {n} {xs : Vector (Expression F) n} :
    constraints_hold.soundness env ((all_zero xs).operations offset) → ∀ x ∈ xs, x.eval env = 0 := by
  intro h_holds x hx
  obtain ⟨_, h_holds⟩ := constraints_hold.forM_vector_soundness' h_holds x hx
  exact h_holds

theorem all_zero.completeness {offset : ℕ} {env : Environment F} {n} {xs : Vector (Expression F) n} :
    (∀ x ∈ xs, x.eval env = 0) → constraints_hold.completeness env ((all_zero xs).operations offset) := by
  intro h_holds
  apply constraints_hold.forM_vector_completeness.mpr
  intro x hx _ _
  exact h_holds x hx

namespace Equality
def main {α : TypeMap} [LawfulProvableType α] (input : Var α F × Var α F) : Circuit F Unit := do
  let (x, y) := input
  let diffs := (to_vars x).zip (to_vars y) |>.map (fun (xi, yi) => xi - yi)
  forM diffs assert_zero

@[reducible]
instance elaborated (α : TypeMap) [LawfulProvableType α] : ElaboratedCircuit F (ProvablePair α α) unit where
  main := main
  local_length _ := 0
  output _ _ := ()

  local_length_eq _ n := by
    rw [main, Vector.forM_toList, Circuit.forM_local_length]
    simp only [ConstantLawfulCircuits.local_length, zero_mul]

  initial_offset_eq _ n := by simp only [main, LawfulCircuit.initial_offset_eq]

def circuit (α : TypeMap) [LawfulProvableType α] : FormalAssertion F (ProvablePair α α) where
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
    simp only [LawfulProvableType.to_elements_from_elements] at h_spec
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
lemma elaborated_eq (α : TypeMap) [LawfulProvableType α] : (circuit α (F:=F)).toElaboratedCircuit = elaborated α := rfl

-- rewrite soundness/completeness directly

@[circuit_norm]
theorem soundness (α : TypeMap) [LawfulProvableType α] (n : ℕ) (env : Environment F) (x y : Var α F) :
    ((circuit α).to_subcircuit n (x, y)).soundness env = (eval env x = eval env y) := by
  simp only [subcircuit_norm, circuit_norm, circuit, forall_const]

@[circuit_norm]
theorem completeness (α : TypeMap) [LawfulProvableType α] (n : ℕ) (env : Environment F) (x y : Var α F) :
    ((circuit α).to_subcircuit n (x, y)).completeness env = (eval env x = eval env y) := by
  simp only [subcircuit_norm, circuit_norm, circuit, true_and]

end Equality
end Gadgets

-- this is exported at the top level because it is a core builtin gadget
@[circuit_norm]
def assert_equals {α : TypeMap} [LawfulProvableType α] (x y : α (Expression F)) : Circuit F Unit :=
  assertion (Gadgets.Equality.circuit α) (x, y)

-- TODO unfortunately, if the inputs to `assert_equals` are just `Expression F`,
-- Lean doesn't come up with `α = id` -- even though `LawfulProvableType` is inferred when `(α:=id)` is passed explicitly.
-- this definition is a somehwat natural alternative that can be used on `Expression F` directly
@[reducible]
def Expression.assert_equals (x y : Expression F) : Circuit F Unit :=
  assertion (Gadgets.Equality.circuit id) (x, y)

-- TODO define a custom syntax e.g. `===` that figures out whether to use `assert_equals` or `Expression.assert_equals`
