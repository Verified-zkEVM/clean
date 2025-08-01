import Clean.Circuit.Basic
import Clean.Circuit.Provable
import Clean.Gadgets.IsZero
import Clean.Utils.Field
import Clean.Utils.Tactics
import Clean.Types.U32

namespace Gadgets.IsZeroU32

variable {p : ℕ} [Fact p.Prime] [p_large_enough: Fact (p > 512)]

/--
Main circuit that checks if a U32 (32-bit unsigned integer) is zero.
Returns 1 if all limbs are 0, otherwise returns 0.
-/
def main (x : Var U32 (F p)) : Circuit (F p) (Var field (F p)) := do
  -- x is zero iff all limbs are zero
  -- We'll use the IsZero gadget for each limb

  -- For each limb, check if it's zero using the IsZero gadget
  let isZero0 ← IsZero.circuit x.x0
  let isZero1 ← IsZero.circuit x.x1
  let isZero2 ← IsZero.circuit x.x2
  let isZero3 ← IsZero.circuit x.x3

  -- The U32 is zero iff all limbs are zero
  let result := isZero0 * isZero1 * isZero2 * isZero3
  return result

instance elaborated : ElaboratedCircuit (F p) U32 field where
  main := main
  localLength _ := 8  -- 4 calls to IsZero.main, each uses 2 witnesses
  localLength_eq := by
    simp [main, circuit_norm, IsZero.circuit, IsZero.elaborated]

def Assumptions (x : U32 (F p)) : Prop := x.Normalized

def Spec (x : U32 (F p)) (output : F p) : Prop :=
  output = if x.value = 0 then 1 else 0

-- Unified theorem about U32 zero representation

lemma U32_value_eq_zero_iff_all_components_zero {p : ℕ} [Fact p.Prime] [Fact (p > 512)]
    {x : U32 (F p)} (h_normalized : x.Normalized) :
    x.value = 0 ↔ x.x0 = 0 ∧ x.x1 = 0 ∧ x.x2 = 0 ∧ x.x3 = 0 := by
  constructor
  · intro h_value_zero
    -- If value = 0, then by injectivity, x = U32.mk 0 0 0 0
    have h_eq : x = U32.mk 0 0 0 0 := by
      apply U32.value_injective_on_normalized
      · exact h_normalized
      · simp [U32.Normalized]
      · rw [h_value_zero]
        simp [U32.value]
    -- Extract components from the equality
    rw [h_eq]
    simp
  · intro ⟨hx0, hx1, hx2, hx3⟩
    simp [U32.value, hx0, hx1, hx2, hx3, ZMod.val_zero]

theorem soundness : Soundness (F p) elaborated Assumptions Spec := by
  circuit_proof_start
  -- U32 is not a ProvableType so the automatic decomposition does not happen
  rcases input
  rename_i input_0 input_1 input_2 input_3
  rcases input_var
  rename_i input_var0 input_var1 input_var2 input_var3
  simp only [IsZero.circuit, IsZero.Assumptions, IsZero.elaborated, explicit_provable_type] at h_holds ⊢
  simp only [circuit_norm, U32.mk.injEq, explicit_provable_type] at h_input
  simp only [h_input, IsZero.Spec] at h_holds
  conv =>
    rhs
    arg 1
    rw [U32_value_eq_zero_iff_all_components_zero (by assumption)]
  aesop

omit p_large_enough in
theorem completeness : Completeness (F p) elaborated Assumptions := by
  circuit_proof_start
  simp [IsZero.circuit, IsZero.Assumptions]

def circuit : FormalCircuit (F p) U32 field := {
  elaborated with Assumptions, Spec, soundness, completeness
}

end Gadgets.IsZeroU32
