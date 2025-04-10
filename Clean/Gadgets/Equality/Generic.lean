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

def Gadgets.all_zero {n} (xs : Vector (Expression (F p)) n) : Circuit (F p) Unit := forM xs assert_zero

theorem Gadgets.AllZero.soundness {offset : ℕ} {env : Environment (F p)} {n} {xs : Vector (Expression (F p)) n} :
    Circuit.constraints_hold.soundness env ((all_zero xs).operations offset) → ∀ x ∈ xs, x.eval env = 0 := by
  intro h_holds
  intro x hx
  unfold all_zero at h_holds
  rw [Circuit.constraints_hold_forM_vector.soundness, List.forall_iff_forall_mem] at h_holds
  rw [←Vector.mem_toList_iff, List.mem_iff_getElem?] at hx
  obtain ⟨ i, hxi ⟩ := hx
  rw [←List.mem_zipIdx_iff_getElem? (x:=(x, i))] at hxi
  specialize h_holds (x, i) hxi
  simp only [circuit_norm] at h_holds
  exact h_holds

namespace Gadgets.Equality
def circuit (α : TypeMap) [ProvableType α] : FormalAssertion (F p) (ProvablePair α α) where
  main (input : Var α (F p) × Var α (F p)) := do
    let (x, y) := input
    let diffs := (to_vars x).zip (to_vars y) |>.map (fun (xi, yi) => xi - yi)
    all_zero diffs

  local_length _ := 0
  local_length_eq _ := by sorry
  initial_offset_eq _ := by sorry

  assumptions _ := True
  spec : α (F p) × α (F p) → Prop
  | (x, y) => x = y

  soundness := by
    intro offset env vars input h_inputs _ h_holds
    replace h_holds := Gadgets.AllZero.soundness h_holds

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
    -- -- introductions
    -- intro n env inputs_var henv inputs h_inputs _ spec
    -- let ⟨⟨x0, x1, x2, x3⟩, ⟨y0, y1, y2, y3⟩⟩ := inputs
    -- let ⟨⟨x0_var, x1_var, x2_var, x3_var⟩, ⟨y0_var, y1_var, y2_var, y3_var⟩⟩ := inputs_var

    -- -- characterize inputs
    -- dsimp only [circuit_norm, eval] at h_inputs
    -- simp only [circuit_norm] at h_inputs
    -- have hx0 : x0_var.eval env = x0 := by injection h_inputs; injections
    -- have hx1 : x1_var.eval env = x1 := by injection h_inputs; injections
    -- have hx2 : x2_var.eval env = x2 := by injection h_inputs; injections
    -- have hx3 : x3_var.eval env = x3 := by injection h_inputs; injections
    -- have hy0 : y0_var.eval env = y0 := by injection h_inputs; injections
    -- have hy1 : y1_var.eval env = y1 := by injection h_inputs; injections
    -- have hy2 : y2_var.eval env = y2 := by injection h_inputs; injections
    -- have hy3 : y3_var.eval env = y3 := by injection h_inputs; injections

    -- have spec0 : x0 = y0 := by injection spec
    -- have spec1 : x1 = y1 := by injection spec
    -- have spec2 : x2 = y2 := by injection spec
    -- have spec3 : x3 = y3 := by injection spec

    -- simp only [circuit_norm, neg_mul, one_mul]
    -- rw [hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    -- rw [spec0, spec1, spec2, spec3]
    -- simp only [add_neg_cancel, and_self]

end Gadgets.Equality
