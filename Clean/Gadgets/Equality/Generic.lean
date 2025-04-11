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

namespace Gadgets
def all_zero {n} (xs : Vector (Expression (F p)) n) : Circuit (F p) Unit := forM xs assert_zero

theorem all_zero.soundness {offset : ℕ} {env : Environment (F p)} {n} {xs : Vector (Expression (F p)) n} :
    Circuit.constraints_hold.soundness env ((all_zero xs).operations offset) → ∀ x ∈ xs, x.eval env = 0 := by
  intro h_holds x hx
  obtain ⟨_, h_holds⟩ := Circuit.constraints_hold_forM_vector.soundness' h_holds x hx
  exact h_holds

namespace Equality
def circuit (α : TypeMap) [ProvableType α] : FormalAssertion (F p) (ProvablePair α α) where
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
    intro offset env vars input h_inputs _ h_holds
    replace h_holds := Gadgets.all_zero.soundness h_holds

    let ⟨x, y⟩ := input
    let ⟨x_var, y_var⟩ := vars
    simp [circuit_norm, eval] at h_inputs
    obtain ⟨ hx, hy ⟩ := h_inputs
    simp only
    rw [←hx, ←hy]
    congr 1
    ext i hi
    simp only [Vector.getElem_map]

    rw [to_vars, ←Vector.forall_getElem] at h_holds
    specialize h_holds i hi
    rw [Vector.getElem_map, Vector.getElem_zip] at h_holds
    simp only [Expression.eval] at h_holds
    rw [neg_one_mul] at h_holds
    exact eq_of_add_neg_eq_zero h_holds

  completeness := by sorry

end Equality
end Gadgets
