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

-- Helper lemma: injectivity of two-component base-256 representation
lemma base256_two_injective (a0 a1 b0 b1 : ℕ) 
    (ha0 : a0 < 256) (hb0 : b0 < 256)
    (h : a0 + 256 * a1 = b0 + 256 * b1) :
    a0 = b0 ∧ a1 = b1 := by
  -- First component: use mod 256
  have h0 : a0 = b0 := by
    have : a0 % 256 = b0 % 256 := by
      calc a0 % 256 = (a0 + 256 * a1) % 256 := by simp [Nat.add_mul_mod_self_left]
        _ = (b0 + 256 * b1) % 256 := by rw [h]
        _ = b0 % 256 := by simp [Nat.add_mul_mod_self_left]
    rw [Nat.mod_eq_of_lt ha0, Nat.mod_eq_of_lt hb0] at this
    exact this
  
  -- Second component: divide by 256
  have h1 : a1 = b1 := by
    have : (a0 + 256 * a1) / 256 = (b0 + 256 * b1) / 256 := by
      rw [h]
    rw [Nat.add_mul_div_left _ _ (by norm_num : 0 < 256)] at this
    rw [Nat.add_mul_div_left _ _ (by norm_num : 0 < 256)] at this
    have ha0_div : a0 / 256 = 0 := Nat.div_eq_zero_iff.mpr (Or.inr ha0)
    have hb0_div : b0 / 256 = 0 := Nat.div_eq_zero_iff.mpr (Or.inr hb0)
    rw [ha0_div, hb0_div] at this
    simp at this
    exact this
  
  exact ⟨h0, h1⟩

-- Injectivity of four-component base-256 representation
lemma base256_four_injective (a0 a1 a2 a3 b0 b1 b2 b3 : ℕ) 
    (ha0 : a0 < 256) (ha1 : a1 < 256) (ha2 : a2 < 256) (_ : a3 < 256)
    (hb0 : b0 < 256) (hb1 : b1 < 256) (hb2 : b2 < 256) (_ : b3 < 256)
    (h : a0 + 256 * (a1 + 256 * (a2 + 256 * a3)) = b0 + 256 * (b1 + 256 * (b2 + 256 * b3))) :
    a0 = b0 ∧ a1 = b1 ∧ a2 = b2 ∧ a3 = b3 := by
  -- Apply base256_two_injective repeatedly
  -- First, view as a0 + 256 * (rest)
  have h_outer := base256_two_injective a0 (a1 + 256 * (a2 + 256 * a3)) 
                                        b0 (b1 + 256 * (b2 + 256 * b3))
                                        ha0 hb0 h
  obtain ⟨h0, h_rest⟩ := h_outer
  
  -- Now apply to the remaining components
  have h_inner := base256_two_injective a1 (a2 + 256 * a3) b1 (b2 + 256 * b3)
                                        ha1 hb1 h_rest
  obtain ⟨h1, h_rest2⟩ := h_inner
  
  -- Finally, the last two components
  have h_final := base256_two_injective a2 a3 b2 b3 ha2 hb2 h_rest2
  obtain ⟨h2, h3⟩ := h_final
  
  exact ⟨h0, h1, h2, h3⟩

lemma U32_value_injective_on_normalized {p : ℕ} [Fact p.Prime] [Fact (p > 512)] (x y : U32 (F p)) 
    (hx : x.Normalized) (hy : y.Normalized) :
    x.value = y.value → x = y := by
  intro h_eq
  -- Use horner form of value
  have hx_value : x.value = x.x0.val + 256 * (x.x1.val + 256 * (x.x2.val + 256 * x.x3.val)) := by
    exact U32.value_horner x
  have hy_value : y.value = y.x0.val + 256 * (y.x1.val + 256 * (y.x2.val + 256 * y.x3.val)) := by
    exact U32.value_horner y
  rw [hx_value, hy_value] at h_eq
  
  -- Extract bounds from normalization
  simp only [U32.Normalized] at hx hy
  have ⟨hx0, hx1, hx2, hx3⟩ := hx
  have ⟨hy0, hy1, hy2, hy3⟩ := hy
  
  -- Apply base256_four_injective
  have ⟨h0, h1, h2, h3⟩ := base256_four_injective _ _ _ _ _ _ _ _ hx0 hx1 hx2 hx3 hy0 hy1 hy2 hy3 h_eq
  
  -- Now show the U32s are equal using ZMod.val_injective
  have hp : 256 < p := by
    have : Fact (p > 512) := inferInstance
    have : p > 512 := this.out
    omega
  
  -- Show equality component by component
  have : x.x0 = y.x0 := ZMod.val_injective (n := p) h0
  have : x.x1 = y.x1 := ZMod.val_injective (n := p) h1
  have : x.x2 = y.x2 := ZMod.val_injective (n := p) h2
  have : x.x3 = y.x3 := ZMod.val_injective (n := p) h3
  
  -- Reconstruct equality
  cases x; cases y
  simp_all

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

omit [Fact (Nat.Prime p)] p_large_enough in
lemma U32_third_component_nonzero (x0 x1 x2 x3 : F p)
    (_ : (U32.mk x0 x1 x2 x3).Normalized) :
    x2 ≠ 0 → (U32.mk x0 x1 x2 x3).value ≠ 0 := by
  intro h_nonzero
  -- Use the horner form of value
  rw [U32.value_horner]
  simp only [U32.mk]
  -- value = x0.val + 2^8 * (x1.val + 2^8 * (x2.val + 2^8 * x3.val))
  intro h_eq
  -- If the entire value is 0, decompose layer by layer
  have h_x0_val : x0.val = 0 := by
    have h_nonneg : 0 ≤ 2^8 * (x1.val + 2^8 * (x2.val + 2^8 * x3.val)) := by
      simp only [mul_nonneg_iff_of_pos_left, pow_pos, zero_lt_two]
      omega
    omega
  -- So we have 2^8 * (x1.val + 2^8 * (x2.val + 2^8 * x3.val)) = 0
  have h_mult_zero : 2^8 * (x1.val + 2^8 * (x2.val + 2^8 * x3.val)) = 0 := by
    rw [h_x0_val, zero_add] at h_eq
    exact h_eq
  -- Since 2^8 ≠ 0, we have x1.val + 2^8 * (x2.val + 2^8 * x3.val) = 0
  have h_inner : x1.val + 2^8 * (x2.val + 2^8 * x3.val) = 0 := by
    have : (2 : ℕ)^8 ≠ 0 := by norm_num
    exact (mul_eq_zero.mp h_mult_zero).resolve_left this
  -- Similarly, x1.val = 0
  have h_x1_val : x1.val = 0 := by
    have h_nonneg : 0 ≤ 2^8 * (x2.val + 2^8 * x3.val) := by
      simp only [mul_nonneg_iff_of_pos_left, pow_pos, zero_lt_two]
      omega
    omega
  -- So 2^8 * (x2.val + 2^8 * x3.val) = 0
  have h_mult_zero2 : 2^8 * (x2.val + 2^8 * x3.val) = 0 := by
    rw [h_x1_val, zero_add] at h_inner
    exact h_inner
  -- Since 2^8 ≠ 0, we have x2.val + 2^8 * x3.val = 0
  have h_inner2 : x2.val + 2^8 * x3.val = 0 := by
    have : (2 : ℕ)^8 ≠ 0 := by norm_num
    exact (mul_eq_zero.mp h_mult_zero2).resolve_left this
  -- Finally, x2.val = 0
  have h_x2_val : x2.val = 0 := by
    have h_nonneg : 0 ≤ 2^8 * x3.val := by
      simp only [mul_nonneg_iff_of_pos_left, pow_pos, zero_lt_two]
      omega
    omega
  -- But x2.val = 0 implies x2 = 0 in F p
  have : x2 = 0 := by
    rw [← ZMod.val_eq_zero]
    exact h_x2_val
  contradiction

omit [Fact (Nat.Prime p)] p_large_enough in
lemma U32_fourth_component_nonzero (x0 x1 x2 x3 : F p)
    (_ : (U32.mk x0 x1 x2 x3).Normalized) :
    x3 ≠ 0 → (U32.mk x0 x1 x2 x3).value ≠ 0 := by
  intro h_nonzero
  -- Use the horner form of value
  rw [U32.value_horner]
  simp only [U32.mk]
  -- value = x0.val + 2^8 * (x1.val + 2^8 * (x2.val + 2^8 * x3.val))
  intro h_eq
  -- If the entire value is 0, decompose layer by layer
  have h_x0_val : x0.val = 0 := by
    have h_nonneg : 0 ≤ 2^8 * (x1.val + 2^8 * (x2.val + 2^8 * x3.val)) := by
      simp only [mul_nonneg_iff_of_pos_left, pow_pos, zero_lt_two]
      omega
    omega
  -- So we have 2^8 * (x1.val + 2^8 * (x2.val + 2^8 * x3.val)) = 0
  have h_mult_zero : 2^8 * (x1.val + 2^8 * (x2.val + 2^8 * x3.val)) = 0 := by
    rw [h_x0_val, zero_add] at h_eq
    exact h_eq
  -- Since 2^8 ≠ 0, we have x1.val + 2^8 * (x2.val + 2^8 * x3.val) = 0
  have h_inner : x1.val + 2^8 * (x2.val + 2^8 * x3.val) = 0 := by
    have : (2 : ℕ)^8 ≠ 0 := by norm_num
    exact (mul_eq_zero.mp h_mult_zero).resolve_left this
  -- Similarly, x1.val = 0
  have h_x1_val : x1.val = 0 := by
    have h_nonneg : 0 ≤ 2^8 * (x2.val + 2^8 * x3.val) := by
      simp only [mul_nonneg_iff_of_pos_left, pow_pos, zero_lt_two]
      omega
    omega
  -- So 2^8 * (x2.val + 2^8 * x3.val) = 0
  have h_mult_zero2 : 2^8 * (x2.val + 2^8 * x3.val) = 0 := by
    rw [h_x1_val, zero_add] at h_inner
    exact h_inner
  -- Since 2^8 ≠ 0, we have x2.val + 2^8 * x3.val = 0
  have h_inner2 : x2.val + 2^8 * x3.val = 0 := by
    have : (2 : ℕ)^8 ≠ 0 := by norm_num
    exact (mul_eq_zero.mp h_mult_zero2).resolve_left this
  -- Similarly, x2.val = 0
  have h_x2_val : x2.val = 0 := by
    have h_nonneg : 0 ≤ 2^8 * x3.val := by
      simp only [mul_nonneg_iff_of_pos_left, pow_pos, zero_lt_two]
      omega
    omega
  -- So 2^8 * x3.val = 0
  have h_mult_zero3 : 2^8 * x3.val = 0 := by
    rw [h_x2_val, zero_add] at h_inner2
    exact h_inner2
  -- Since 2^8 ≠ 0, we have x3.val = 0
  have h_x3_val : x3.val = 0 := by
    have : (2 : ℕ)^8 ≠ 0 := by norm_num
    exact (mul_eq_zero.mp h_mult_zero3).resolve_left this
  -- But x3.val = 0 implies x3 = 0 in F p
  have : x3 = 0 := by
    rw [← ZMod.val_eq_zero]
    exact h_x3_val
  contradiction

omit p_large_enough in
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
