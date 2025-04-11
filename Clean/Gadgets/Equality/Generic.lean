import Mathlib.Algebra.Field.Basic
import Mathlib.Data.ZMod.Basic
import Clean.Utils.Primes
import Clean.Utils.Vector
import Clean.Circuit.Expression
import Clean.Circuit.Provable
import Clean.Circuit.Basic
import Clean.Circuit.Lawful
import Clean.Utils.Field
import Clean.Types.U32

section
variable {p : ℕ} [Fact p.Prime]
open Circuit (constraints_hold)

namespace Gadgets
def all_zero {n} (xs : Vector (Expression (F p)) n) : Circuit (F p) Unit := forM xs assert_zero

theorem all_zero.soundness {offset : ℕ} {env : Environment (F p)} {n} {xs : Vector (Expression (F p)) n} :
    constraints_hold.soundness env ((all_zero xs).operations offset) → ∀ x ∈ xs, x.eval env = 0 := by
  intro h_holds x hx
  obtain ⟨_, h_holds⟩ := constraints_hold.forM_vector_soundness' h_holds x hx
  exact h_holds

theorem all_zero.completeness {offset : ℕ} {env : Environment (F p)} {n} {xs : Vector (Expression (F p)) n} :
    (∀ x ∈ xs, x.eval env = 0) → constraints_hold.completeness env ((all_zero xs).operations offset) := by
  intro h_holds
  apply constraints_hold.forM_vector_completeness.mpr
  intro x hx _ _
  exact h_holds x hx

namespace Equality

def circuit (α : TypeMap) [LawfulProvableType α] : FormalAssertion (F p) (ProvablePair α α) where
  main (input : Var α (F p) × Var α (F p)) := do
    let (x, y) := input
    let diffs := (to_vars x).zip (to_vars y) |>.map (fun (xi, yi) => xi - yi)
    forM diffs assert_zero

  assumptions _ := True

  spec : α (F p) × α (F p) → Prop
  | (x, y) => x = y

  local_length_eq _ n := by
    simp only
    rw [Vector.forM_toList, Circuit.forM_local_length]
    simp only [ConstantLawfulCircuits.local_length, zero_mul]

  initial_offset_eq _ n := by simp only [LawfulCircuit.initial_offset_eq]

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
    simp only [circuit_norm, Prod.mk.injEq] at h_input
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

end Equality

def assert_equals {α : TypeMap} [LawfulProvableType α] (x y : Var α (F p)) : Circuit (F p) Unit :=
  assertion (Equality.circuit α) (x, y)
end Gadgets
