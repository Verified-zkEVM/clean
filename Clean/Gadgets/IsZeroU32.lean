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

omit [Fact (Nat.Prime p)] p_large_enough in
lemma U32_first_component_nonzero (x0 x1 x2 x3 : F p)
    (_ : (U32.mk x0 x1 x2 x3).Normalized) :
    x0 ≠ 0 → (U32.mk x0 x1 x2 x3).value ≠ 0 := by
  intro h_nonzero
  -- Use the horner form of value
  rw [U32.value_horner]
  simp only [U32.mk]
  -- If x0.val ≠ 0, then x0.val + 2^8 * (...) ≠ 0
  intro h_eq
  -- From h_eq: x0.val + 2^8 * (...) = 0
  -- Since all terms are natural numbers, this means x0.val = 0
  have h_x0_val : x0.val = 0 := by
    have h_nonneg : 0 ≤ 2^8 * (x1.val + 2^8 * (x2.val + 2^8 * x3.val)) := by
      simp only [mul_nonneg_iff_of_pos_left, pow_pos, zero_lt_two]
      omega
    omega
  -- But x0.val = 0 implies x0 = 0 in F p
  have : x0 = 0 := by
    rw [← ZMod.val_eq_zero]
    exact h_x0_val
  contradiction

omit [Fact (Nat.Prime p)] p_large_enough in
lemma U32_second_component_nonzero (x0 x1 x2 x3 : F p)
    (_ : (U32.mk x0 x1 x2 x3).Normalized) :
    x1 ≠ 0 → (U32.mk x0 x1 x2 x3).value ≠ 0 := by
  intro h_nonzero
  -- Use the horner form of value
  rw [U32.value_horner]
  simp only [U32.mk]
  -- value = x0.val + 2^8 * (x1.val + 2^8 * (x2.val + 2^8 * x3.val))
  intro h_eq
  -- If the entire value is 0, then both x0.val = 0 and the multiplied term = 0
  have h_x0_val : x0.val = 0 := by
    have h_nonneg : 0 ≤ 2^8 * (x1.val + 2^8 * (x2.val + 2^8 * x3.val)) := by
      simp only [mul_nonneg_iff_of_pos_left, pow_pos, zero_lt_two]
      omega
    omega
  -- So we have 2^8 * (x1.val + 2^8 * (x2.val + 2^8 * x3.val)) = 0
  have h_mult_zero : 2^8 * (x1.val + 2^8 * (x2.val + 2^8 * x3.val)) = 0 := by
    rw [h_x0_val, zero_add] at h_eq
    exact h_eq
  -- Since 2^8 ≠ 0, we must have x1.val + 2^8 * (x2.val + 2^8 * x3.val) = 0
  have h_inner : x1.val + 2^8 * (x2.val + 2^8 * x3.val) = 0 := by
    have : (2 : ℕ)^8 ≠ 0 := by norm_num
    exact (mul_eq_zero.mp h_mult_zero).resolve_left this
  -- By similar reasoning, x1.val = 0
  have h_x1_val : x1.val = 0 := by
    have h_nonneg : 0 ≤ 2^8 * (x2.val + 2^8 * x3.val) := by
      simp only [mul_nonneg_iff_of_pos_left, pow_pos, zero_lt_two]
      omega
    omega
  -- But x1.val = 0 implies x1 = 0 in F p
  have : x1 = 0 := by
    rw [← ZMod.val_eq_zero]
    exact h_x1_val
  contradiction

lemma U32_third_component_nonzero (x0 x1 x2 x3 : F p)
    (h_normalized : (U32.mk x0 x1 x2 x3).Normalized) :
    x2 ≠ 0 → (U32.mk x0 x1 x2 x3).value ≠ 0 := by sorry

lemma U32_fourth_component_nonzero (x0 x1 x2 x3 : F p)
    (h_normalized : (U32.mk x0 x1 x2 x3).Normalized) :
    x3 ≠ 0 → (U32.mk x0 x1 x2 x3).value ≠ 0 := by sorry

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
  by_cases h0 : input_0 ≠ 0
  · simp only [h0] at *
    norm_num at h_holds
    simp only [h_holds]
    norm_num
    rw [if_neg]
    apply U32_first_component_nonzero <;> assumption
  by_cases h1 : input_1 ≠ 0
  · simp only [h1] at *
    norm_num at h_holds
    simp only [h_holds]
    norm_num
    rw [if_neg]
    apply U32_second_component_nonzero <;> assumption
  by_cases h2 : input_2 ≠ 0
  · simp only [h2] at *
    norm_num at h_holds
    simp only [h_holds]
    norm_num
    rw [if_neg]
    apply U32_third_component_nonzero <;> assumption
  by_cases h3 : input_3 ≠ 0
  · simp only [h3] at *
    norm_num at h_holds
    simp only [h_holds]
    norm_num
    rw [if_neg]
    apply U32_fourth_component_nonzero <;> assumption
  norm_num at h0 h1 h2 h3
  simp only [h0, h1, h2, h3] at h_holds ⊢
  simp_all only []
  norm_num
  simp only [U32.value, ZMod.val_zero, zero_mul, add_zero, Nat.reducePow, ↓reduceIte]

omit p_large_enough in
theorem completeness : Completeness (F p) elaborated Assumptions := by
  circuit_proof_start
  simp [IsZero.circuit, IsZero.Assumptions]

def circuit : FormalCircuit (F p) U32 field := {
  elaborated with Assumptions, Spec, soundness, completeness
}

end Gadgets.IsZeroU32
