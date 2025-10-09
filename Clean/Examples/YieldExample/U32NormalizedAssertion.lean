import Clean.Circuit.Basic
import Clean.Types.U32
import Clean.Utils.Tactics

namespace Examples.YieldExample.U32NormalizedAssertion

variable {p : ℕ} [Fact p.Prime]

/--
Main circuit that uses yielded byte values to check U32 normalization
-/
def main (input : Var U32 (F p)) : Circuit (F p) Unit := do
  -- Use the yielded byte values for each limb
  use (NamedList.mk "byte" [input.x0])
  use (NamedList.mk "byte" [input.x1])
  use (NamedList.mk "byte" [input.x2])
  use (NamedList.mk "byte" [input.x3])
  return ()

def elaborated : ElaboratedCircuit (F p) U32 unit where
  main
  localLength _ := 0
  localLength_eq := by simp [circuit_norm, main]
  yields _ _ _ := ∅
  yields_eq := by intros; simp [circuit_norm, main]
  subcircuitsConsistent := by simp [circuit_norm, main]

/--
Assumptions:
1. All yielded "byte" NamedLists with single element must have value < 256 (for soundness)
2. All bytes [0..255] are in the yielded set (for completeness)
-/
def Assumptions (_ : U32 (F p)) (yielded : Set (NamedList (F p))) : Prop :=
  (∀ (v : F p), NamedList.mk "byte" [v] ∈ yielded → v.val < 256) ∧
  (∀ (n : Nat), n < 256 → NamedList.mk "byte" [(n : F p)] ∈ yielded)

/--
Spec: The U32 input is normalized
-/
def Spec (input : U32 (F p)) : Prop :=
  input.Normalized

theorem soundness : FormalAssertion.Soundness (F p) elaborated Assumptions Spec := by
  circuit_proof_start
  -- After circuit_proof_start, we need to prove Spec input
  -- The constraints from `use` ensure each limb is in the yielded set
  -- The first part of Assumptions ensures all yielded bytes have value < 256
  -- Therefore all limbs have value < 256, so U32 is normalized
  simp only [U32.Normalized]
  obtain ⟨h_sound, h_complete⟩ := h_assumptions
  obtain ⟨h_use0, h_use1, h_use2, h_use3⟩ := h_holds
  -- Each h_use says the corresponding limb's NamedList is in yielded
  -- Apply h_sound to get that each limb < 256
  have h0 := h_sound input.x0 (by aesop)
  have h1 := h_sound input.x1 (by aesop)
  have h2 := h_sound input.x2 (by aesop)
  have h3 := h_sound input.x3 (by aesop)
  exact ⟨h0, h1, h2, h3⟩

theorem completeness : FormalAssertion.Completeness (F p) elaborated Assumptions Spec := by
  circuit_proof_start
  -- We need to prove the constraints hold given Assumptions AND Spec
  obtain ⟨h_sound, h_complete⟩ := h_assumptions
  simp only [U32.Normalized] at h_spec
  obtain ⟨h0, h1, h2, h3⟩ := h_spec
  -- The use constraints require each limb's NamedList to be in yielded
  -- We need to simplify NamedList.eval env { name := "byte", values := [input_var.xi] }
  simp only [NamedList.eval, List.map]
  -- Now we need to use h_input: eval env input_var = input
  -- This means Expression.eval env input_var.xi = input.xi
  have h_x0 : Expression.eval env input_var.x0 = input.x0 := by
    simp only [← h_input]
    rfl
  have h_x1 : Expression.eval env input_var.x1 = input.x1 := by
    simp only [← h_input]
    rfl
  have h_x2 : Expression.eval env input_var.x2 = input.x2 := by
    simp only [← h_input]
    rfl
  have h_x3 : Expression.eval env input_var.x3 = input.x3 := by
    simp only [← h_input]
    rfl
  simp only [h_x0, h_x1, h_x2, h_x3]
  constructor
  · -- First use constraint for x0
    -- We need { name := "byte", values := [input.x0] } ∈ yielded
    -- Since input.x0.val < 256 (from h0), we can apply h_complete
    -- We need to show input.x0 = ↑(input.x0.val)
    have : input.x0 = (input.x0.val : F p) := by
      conv_lhs => rw [← ZMod.natCast_zmod_val input.x0]
    rw [this]
    apply h_complete
    exact h0
  constructor
  · -- Second use constraint for x1
    have : input.x1 = (input.x1.val : F p) := by
      conv_lhs => rw [← ZMod.natCast_zmod_val input.x1]
    rw [this]
    apply h_complete
    exact h1
  constructor
  · -- Third use constraint for x2
    have : input.x2 = (input.x2.val : F p) := by
      conv_lhs => rw [← ZMod.natCast_zmod_val input.x2]
    rw [this]
    apply h_complete
    exact h2
  · -- Fourth use constraint for x3
    have : input.x3 = (input.x3.val : F p) := by
      conv_lhs => rw [← ZMod.natCast_zmod_val input.x3]
    rw [this]
    apply h_complete
    exact h3

def assertion : FormalAssertion (F p) U32 := {
  elaborated with
  Assumptions, Spec, soundness, completeness
}

end Examples.YieldExample.U32NormalizedAssertion
