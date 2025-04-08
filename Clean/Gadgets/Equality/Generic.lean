import Mathlib.Algebra.Field.Basic
import Mathlib.Data.ZMod.Basic
import Clean.Utils.Primes
import Clean.Utils.Vector
import Clean.Circuit.Expression
import Clean.Circuit.Provable
import Clean.Circuit.Basic
import Clean.Circuit.Operations
import Clean.Utils.Field
import Clean.Types.U32

section
variable {p : ℕ} [Fact p.Prime]

namespace Gadgets.Equality

def all_equal {n} (l : Vector (Expression (F p) × Expression (F p)) n) : Circuit (F p) Unit :=
  forM l fun (x, y) => assert_zero (x - y)

theorem soundness (offset : ℕ) (env : Environment (F p)) {n} (l : Vector (Expression (F p) × Expression (F p)) n)
  (ctx : OperationsList (F p)) :
  (Circuit.constraints_hold.soundness env ((all_equal l).operations offset)) →
    (∀ t ∈ l, match t with | (x,y) => x.eval env = y.eval env) := by
  intro h_holds (x,y) ht
  induction l using Vector.induct_push with
  | nil => simp at ht
  | push ts t ih =>
    simp_all [all_equal]
    rw [←Vector.append_singleton, Vector.forM_append, Vector.forM_mk,
      Vector.forM_mk, List.forM_toArray [t],
      List.forM_eq_forM, List.forM_cons, List.forM_nil,
      ] at h_holds
    dsimp only [Circuit.operations] at h_holds
    have : (do
          assert_zero (t.1 - t.2)
          pure PUnit.unit) = assert_zero (t.1 - t.2) := rfl
    rw [this] at h_holds; clear this
    rw [Circuit.assert_zero_appends] at h_holds
    rcases ht with ht|ht
    repeat sorry

def circuit (α : TypeMap) [ProvableType α] : FormalAssertion (F p) (ProvablePair α α) where
  main (input : Var α (F p) × Var α (F p)) := do
    let (x, y) := input
    List.forM (.zip (to_vars x).toList (to_vars y).toList) fun (xi, yi) =>
      assert_zero (xi - yi)

  local_length _ := 0
  local_length_eq _ := by sorry
  initial_offset_eq _ := by sorry

  assumptions _ := true
  spec : α (F p) × α (F p) → Prop
  | (x, y) => x = y

  soundness := by
    intro offset env vars input h_inputs _ h_holds
    let ⟨x, y⟩ := input
    let ⟨x_var, y_var⟩ := vars
    simp [circuit_norm, eval] at h_inputs
    obtain ⟨ hx, hy ⟩ := h_inputs
    dsimp
    rw [←hx, ←hy]
    congr 1
    rw [Vector.ext_iff]
    simp [Vector.getElem_map]
    dsimp at h_holds
    -- suffices h :
    --     ∀ l : List (Expression (F p) × Expression (F p)),
    --     Circuit.constraints_hold.soundness env ((forM l (fun (x, y) => assert_zero (x - y))).operations ctx) →
    --     (∀ t ∈ l, match t with | (x,y) => x.eval env = y.eval env) by sorry

    sorry
    -- done

    -- set l := (to_elements x_var).toList.zip (to_elements y_var).toList
    -- induction l generalizing h_holds with
    -- | nil => simp only
    -- | cons a as ih => sorry
    -- rcases h_holds with ⟨⟨⟨eq0, eq1⟩, eq2⟩, eq3⟩
    -- rw [eq0, eq1, eq2, eq3]

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
